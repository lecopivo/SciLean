import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionTransformations
import SciLean.Core.Meta.GenerateInit
import SciLean.Tactic.LetNormalize

namespace SciLean.Meta

open Lean Meta Qq

namespace GenerateProperty

/-- Returns `(id, u, K)` where `K` is infered field type with universe level `u`

The index `id` tells that arguments `args[id:]` have already `K` in its local context with valid `IsROrC K` instances. -/
def getFieldOutOfContextQ (args : Array Expr) : MetaM (Option ((u : Level) × (K : Q(Type $u)) × Q(IsROrC $K))) := do

  let mut K? : Option Expr := none
  for arg in args do
    let type ← inferType arg

    if type.isAppOf ``IsROrC then
      K? := type.getArg! 0
      break

    if type.isAppOf ``Scalar then
      K? := type.getArg! 0
      break

    if type.isAppOf ``RealScalar then
      K? := type.getArg! 0
      break

    if type.isAppOf ``Vec then
      K? := type.getArg! 0
      break

    if type.isAppOf ``SemiInnerProductSpace then
      K? := type.getArg! 0
      break

    if type.isAppOf ``SemiHilbert then
      K? := type.getArg! 0
      break

    if type.isAppOf ``FinVec then
      K? := type.getArg! 1
      break

  let .some K := K? | return none
  let .some ⟨u,K⟩ ← isTypeQ K | return none
  let isROrC ← synthInstanceQ q(IsROrC $K)

  return .some ⟨u,K,isROrC⟩


/-- Split free variables to "context variables" and "arguments"

- context variables: types, instance, implicit fvars
- arguments: explicit non-type fvars

It is assumed that all "context variables" are before "arguments"
-/
def splitToCtxAndArgs (xs : Array Expr) : MetaM (Array Expr × Array Expr) := do
  let mut i := 0
  for x in xs do
    let X ← inferType x
    if (← x.fvarId!.getBinderInfo) == .default && 
       ¬X.bindingBodyRec.isType then
      break
    i := i + 1

  -- check that the rest of arguments is ok
  for j in [i:xs.size] do
    let x := xs[j]!
    let X ← inferType x
    if (← x.fvarId!.getBinderInfo) != .default then
      throwError "function has invalid signature, undexpected non-explicit argument `({← ppExpr x} : {← ppExpr X})`"
    if X.bindingBodyRec.isType then
      throwError "function has invalid signature, undexpected type argument `({← ppExpr x} : {← ppExpr X})`"

  return (xs[0:i],xs[i:])



/-- We clasify arguments into three kinds
- main: arguments we want to differentiate with respect to
- trailing: arguments that should appear in the return type e.g. `i` is trailing in `<∂ xs, fun i => getElem xs i`
- unused: all other arguments
-/
inductive  ArgKind where
  | main (i : Nat)
  | unused (i : Nat)
  | trailing (i : Nat)

/-- split arguments into main, unused and trailing by providing names of main and trailing args -/
def splitArgs (args : Array Expr) (mainNames trailingNames : Array Name)
  : MetaM (Array Expr × Array Expr × Array Expr × Array ArgKind) := do 
  
  let mut main : Array Expr := #[]
  let mut unused : Array Expr := #[]
  let mut trailing : Array Expr := #[]

  let mut argKind : Array ArgKind := #[]

  for arg in args do
    let name ← arg.fvarId!.getUserName
    if mainNames.contains name then
      argKind := argKind.push (.main main.size)
      main := main.push arg
    else if trailingNames.contains name then
      if mainNames.contains name then
        throwError "argument {name} can't be main and trailing argument at the same time"
      argKind := argKind.push (.trailing trailing.size)
      trailing := trailing.push arg
    else
      argKind := argKind.push (.unused unused.size)
      unused := unused.push arg

  if main.size ≠ mainNames.size then
    throwError "unrecoginezed main argument, TODO: determine which one"

  if trailing.size ≠ trailingNames.size then
    throwError "unrecoginezed trailing argument, TODO: determine which one"
  
  return (main, unused, trailing, argKind)

def mergeArgs (main unused trailing : Array Expr) (argKinds : Array ArgKind) : Array Expr := Id.run do
  let mut args : Array Expr := #[]
  for argKind in argKinds do
    match argKind with
    | .main i => args := args.push main[i]!
    | .unused i => args := args.push unused[i]!
    | .trailing i => args := args.push trailing[i]!
  return args

def mergeArgs' (main unused : Array Expr) (argKinds : Array ArgKind) : Array Expr := Id.run do
  let mut args : Array Expr := #[]
  for argKind in argKinds do
    match argKind with
    | .main i => args := args.push main[i]!
    | .unused i => args := args.push unused[i]!
    | .trailing _ => continue
  return args


/-- Check that types of `ys` do not depend on fvars `xs` -/
def checkNoDependentTypes (xs ys : Array Expr) : MetaM Unit := do
  for y in ys do
    let Y ← inferType y
    if let .some x := xs.find? (fun x => Y.containsFVar x.fvarId!) then
      throwError s!"the type of ({← ppExpr y} : {← ppExpr (← inferType y)}) depends on the argument {← ppExpr x}, dependent types like this are not supported"
