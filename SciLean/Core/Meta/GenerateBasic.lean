import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionTransformations
import SciLean.Core.Meta.GenerateInit
import SciLean.Data.ArrayType.Notation
import SciLean.Tactic.LetNormalize

namespace SciLean.Meta

open Lean Meta Qq

namespace GenerateProperty


open Elab Lean.Parser.Tactic in
def elabProof (goal : Expr) (tac : TSyntax ``tacticSeq) : TermElabM Expr := do

  let proof ← mkFreshExprMVar goal
  let goals ← Tactic.run proof.mvarId! do
    Tactic.evalTactic tac

  if ¬goals.isEmpty then
    throwError s!"failed to prove {← ppExpr goal}\nunsolved goals {← liftM <| goals.mapM (fun m => m.getType >>= ppExpr)}"
  
  return ← instantiateMVars proof

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
      K? := type.getArg! 1
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

    if type.isAppOf ``arrayTypeCont then
      K? := type.getArg! 1
      break

    if type.isAppOf ``Float then
      K? := type
      break

    if type.isAppOf ``Real then
      K? := type
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

  -- -- check that the rest of arguments is ok
  -- for j in [i:xs.size] do
  --   let x := xs[j]!
  --   let X ← inferType x
  --   if (← x.fvarId!.getBinderInfo) != .default then
  --     throwError "function has invalid signature, undexpected non-explicit argument `({← ppExpr x} : {← ppExpr X})`"
  --   if X.bindingBodyRec.isType then
  --     throwError "function has invalid signature, undexpected type argument `({← ppExpr x} : {← ppExpr X})`"

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

structure GenerateData where
  /-- field over which we are currently working -/
  K : Expr
  
  /-- original context fvars of a function, these are types, instances and implicit arguments -/
  orgCtx : Array Expr 
  /-- extended orgCtx such that types form appropriate vector space, group or whatever is necessary -/
  ctx : Array Expr 

  /-- main fvars, main arguments we perform function transformation in -/
  mainArgs : Array Expr
  /-- unused fvars -/
  unusedArgs : Array Expr
  /-- trailing fvars -/
  trailingArgs : Array Expr
  /-- argument kinds, this allows to glue arguments back together with mergeArgs and mergeArgs' -/
  argKinds : Array ArgKind

  /-- names of main arguments guaranteed to be in the same order as mainArgs -/
  mainNames : Array Name

  /-- auxiliary type we perform transformation in -/
  W : Expr
  /-- fvar of type W -/
  w : Expr
  /-- fvars making W into vector space, group, or what ever is necessary -/
  ctxW : Array Expr

  /-- function we are working with as a function of `w` -/
  f : Expr
 
  /-- fvars that that are main arguments parametrized by W-/
  argFuns : Array Expr
  /-- fvars for properties about argFun -/
  argFunProps : Array Expr

  /-- declaration suffix based on argument names used to generate rule name -/
  declSuffix : String
  
  /-- level parameters -/
  levelParams : List Name
