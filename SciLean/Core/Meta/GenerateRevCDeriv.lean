import SciLean.Core.Objects.FinVec
import SciLean.Core.FunctionTransformations
import SciLean.Core.Notation
import SciLean.Core.Meta.GenerateInit

namespace SciLean.Meta

open Lean Meta Qq


def isTypeQ (e : Expr) : MetaM (Option ((u : Level) × Q(Type $u))) := do
  let u ← mkFreshLevelMVar
  let .some e ← checkTypeQ e q(Type $u)
    | return none
  return .some ⟨u, e⟩

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

def firstExplicitNonTypeIdx (xs : Array Expr) : MetaM Nat := do
  let mut i := 0
  for x in xs do
    let X ← inferType x
    if (← x.fvarId!.getBinderInfo) == .default && 
       ¬X.bindingBodyRec.isType then
      return i
    i := i + 1
  return i

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

/-- Introduce new fvars such that the type `type` have instance of `SemiInnerProductSpace K ·` -/
partial def extendContextForType {α : Type _}
  {u} (K : Q(Type $u)) (type : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let cls ← mkAppM ``SemiInnerProductSpace #[K, type]
  match ← synthInstance? cls with
  | .some _ => k #[]
  | none => loop type #[]
where 
  loop (T : Expr) (acc : Array Expr) : MetaM α := do
    match T with
    | .forallE _ X Y _ =>
      if Y.hasLooseBVars then
        throwError "can't extend context for dependent type `{← ppExpr T}`"
      let .some ⟨v,X⟩ ← isTypeQ X
        | throwError "invalid type {← ppExpr X}"
      let cls := (Expr.const ``EnumType [v,u,u]).app X
      match ← synthInstance? cls with
      | .some _ => loop Y acc
      | none => 
        withLocalDecl `inst .default cls fun inst =>
          loop Y (acc.push inst)
    | .fvar _ => 
      let cls ← mkAppM ``SemiInnerProductSpace #[K, T]
      match ← synthInstance? cls with
      | .some _ => k acc
      | none => 
        withLocalDecl `inst .default cls fun inst => 
          k (acc.push inst)
    | _ => 
      throwError "dont' know how to extend context for the type `{← ppExpr T}`"

/-- Introduce new fvars such that every type in `types` have instance of `SemiInnerProductSpace K ·` -/
partial def extendContextImpl {α : Type _}
  {u} (K : Q(Type $u)) (types : Array Expr)
  (k : Array Expr → MetaM α) : MetaM α :=
  loop 0 #[]
where 
  loop (i : Nat) (acc : Array Expr) : MetaM α := do
    if h : i < types.size then
      let type := types[i]
      extendContextForType K type fun xs => loop (i+1) (acc ++ xs)
    else
      k acc

def extendContext {α : Type _} [MonadControlT MetaM n] [Monad n]
  {u} (K : Q(Type $u)) (types : Array Expr) (k : Array Expr → n α) : n α :=
  map1MetaM (fun k => extendContextImpl K types k) k

def _root_.Lean.LocalContext.toString (lctx : LocalContext) : MetaM String :=
  lctx.decls.toArray.joinlM 
    (fun decl? => do
      let .some decl := decl? | return ""
      return s!"{decl.userName} : {← ppExpr decl.type}")
    (fun a b => pure (a++"\n"++b))

/-- Extends the set of free variables `xs` such that every type of `xs[i]` has instance `SemiInnerProductSpace K ·` for `i ∈ ids`.  -/
def extendToCorrectContextImpl (K : Expr) (ids : ArraySet Nat) (xs : Array Expr) (type : Expr)
  (k : Array Expr → MetaM α) : MetaM α := do

  let (args, otherArgs, splitIds) := xs.splitIdx (fun i _ => i.1 ∈ ids)
  let idx ← firstExplicitNonTypeIdx xs

  
  sorry
  

/-- Checks that type `X` has instance of `SemiInnerProductSpace K ·`. Throws error if instance does not exists. 

TODO: return suggested class to make this succeed. 
For example:
- for `X = α` suggest class `SemiInnerProductSpace K α`
- for `X = ι → α` suggest classes `EnumType ι` and `SemiInnerProductSpace K α`.
- for `X = DataArrayN α ι` suggest classes `Index ι` and `SemiInnerProductSpace K α`.
-/
def  checkObjInstances (K : Expr) (X : Expr) : MetaM Unit := do
  -- check that return type form SemiInnerProductSpace
  let cls ← mkAppM ``SemiInnerProductSpace #[K, X]
  let .some _semiInnerProductSpace ← synthInstance? cls
    | throwError "unable to synthesize `{← ppExpr cls}` in the context\n{← (← getLCtx).toString}"

/-- Checks that types of `xᵢ` and `b` has instances of `SemiInnerProductSpace K ·`. Throws error if instance does not exists.
 -/
def  checkArgInstances (K : Expr) (xs : Array Expr) : MetaM Unit := do
  -- check that all arguments form SemiInnerProductSpace
  for x in xs do
    let X ← inferType x
    checkObjInstances K X
     

/-- Check that types of `ys` do not depend on fvars `xs` -/
def checkNoDependentTypes (xs ys : Array Expr) : MetaM Unit := do
  for y in ys do
    let Y ← inferType y
    if let .some x := xs.find? (fun x => Y.containsFVar x.fvarId!) then
      throwError s!"the type of ({← ppExpr y} : {← ppExpr (← inferType y)}) depends on the argument {← ppExpr x}, dependent types like this are not supported"
 

/-- Make local declarations is we have an array of names and types. -/
def mkLocalDecls [MonadControlT MetaM n] [Monad n] 
  (names : Array Name) (bi : BinderInfo) (types : Array Expr) : Array (Name × BinderInfo × (Array Expr → n Expr)) :=
  types.mapIdx (fun i type => (names[i]!, bi, fun _ : Array Expr => pure type))


/-- Gives a name based on `baseName` that's not already in the list. -/
private partial def mkUnusedName (names : List Name) (baseName : Name) : Name :=
  if not (names.contains baseName) then
    baseName
  else
    let rec loop (i : Nat := 0) : Name :=
      let w := Name.appendIndexAfter baseName i
      if names.contains w then
        loop (i + 1)
      else
        w
    loop 1

/-- 
Replaces `<∂ fᵢ x` with `Tfᵢ` in `e`
- `argFuns = #[f₁, ..., fₙ]`
- `transArgFuns = #[<∂ f₁ x, ..., <∂ fₙ x]`
- `transArgFunVars  = #[Tf₁, ..., Tfₙ]`

Throws an error if all `fᵢ` has not been liminated from `e`
-/
def eliminateTransArgFun (e : Expr) (argFuns transArgFuns transArgFunVars : Array Expr) : MetaM Expr := do
  let e' ←
    e.replaceM (fun x => do
      if x.hasLooseBVars then
        pure .noMatch
      else
        if let .some i ← transArgFuns.findIdxM? (isDefEq · x) then
          pure (.yield transArgFunVars[i]!)
        else 
          pure .noMatch)

  if let .some i := argFuns.findIdx? (fun argFun => e'.containsFVar argFun.fvarId!) then
    throwError "Failed to elimate {← ppExpr argFuns[i]!} out of transformed function{←ppExpr e}\n it is expected that {← ppExpr argFuns[i]!} appears only in {← ppExpr transArgFuns[i]!}"

  return e'

open Lean Elab Term

def generateRevCDeriv (constName : Name) (argIds : ArraySet Nat) (conv : TSyntax `conv) : TermElabM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs type => do

    let (args, otherArgs, splitIds) := xs.splitIdx (fun i _ => i.1 ∈ argIds)

    let xsNames ← getConstArgNames constName true
    let argNames := argIds.toArray.map (fun i => xsNames[i]!)
    let argName := "arg_" ++ argNames.foldl (init := "") (·++ toString ·)

    trace[Meta.generate_ftrans] "generating revCDeriv for {constName} in arguments {← args.mapM fun arg => do pure s!"({←ppExpr arg} : {← ppExpr (← inferType arg)})"}"

    let .some ⟨_u,K,_isROrC⟩ ← getFieldOutOfContextQ xs
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    -- few checks that we can do what we want to do
    checkObjInstances K type
    checkArgInstances K args
    checkNoDependentTypes args xs

    let vLvlName := mkUnusedName info.levelParams `w
    -- let v ← mkFreshLevelMVar
    let v := Level.param vLvlName
    withLocalDeclQ `W .implicit q(Type $v) fun W => do
    withLocalDecl `instW .instImplicit (← mkAppM ``SemiInnerProductSpace #[K,W]) fun instW => do
    withLocalDeclQ (u:=v) `w .default W fun w => do

    -- argFuns are selected arguments parametrized by `W`
    let argFunDecls :=
      mkLocalDecls argNames .default (← args.mapM fun arg => do mkArrow W (← inferType arg))

    withLocalDecls argFunDecls fun argFuns => do

      let argFunApps := argFuns.map (fun argFun => argFun.app w)

      let lhs ← 
        withLetDecls argNames argFunApps fun args' => do
          let xs' := Array.mergeSplit splitIds args' otherArgs
          let f ← mkLambdaFVars ((#[w] : Array Expr) ++ args') (← mkAppOptM constName (xs'.map Option.some))
          mkAppM ``revCDeriv #[K,f]

      trace[Meta.generate_ftrans] "lhs for revCDeriv rule\n{← ppExpr lhs}"

      let argFunPropDecls ← 
        argFuns.mapM (fun argFun => do
          let name := (← argFun.fvarId!.getUserName).appendBefore "h"
          let bi : BinderInfo := .default
          let type ← mkAppM ``HasAdjDiff #[K,argFun]
          pure (name, bi, fun _ : Array Expr => pure (f:=TermElabM) type))

      withLocalDecls argFunPropDecls fun argFunProps => do

      let (rhs, proof) ← elabConvRewrite lhs conv

      trace[Meta.generate_ftrans] "rhs for revCDeriv rule\n{← ppExpr rhs}"

      let .lam _ _ b _ := rhs
        | throwError "transformed function should be in the form `fun w => ...` but got\n{← ppExpr rhs}"

      let b := b.instantiate1 w

      let transArgFuns ← argFuns.mapM (fun argFun => mkAppM ``revCDeriv #[K, argFun, w])

      let transArgNames := argNames.map (fun n => n.appendAfter "d" |>.appendAfter (toString n))
      let transArgFunDecls := 
        mkLocalDecls transArgNames .default (← liftM <| transArgFuns.mapM inferType)

      withLocalDecls transArgFunDecls fun transArgFunVars => do

      -- find all occurances of `<∂ (w':=w), argFunᵢ w` and replace it with recently introduced fvar
      let b' ← eliminateTransArgFun b argFuns transArgFuns transArgFunVars
      if b'.containsFVar w.fvarId! then
        throwError s!"transformed function {← ppExpr b'} still contains {← ppExpr w}"

      let idx ← firstExplicitNonTypeIdx xs

      let xs' := Array.mergeSplit splitIds transArgFunVars otherArgs
      let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
      let transFun ← instantiateMVars (← mkLambdaFVars fvars b')
      let transFunName := constName.append argName |>.append "revCDeriv"
      trace[Meta.generate_ftrans] "generated revCDeriv function {transFunName}\n{← ppExpr transFun}"

      let transFunInfo : DefinitionVal := 
      {
        name  := transFunName
        type  := (← inferType transFun)
        value := transFun
        hints := .regular 0
        safety := .safe
        levelParams := vLvlName :: info.levelParams
      }

      addAndCompile (.defnDecl transFunInfo)

      let xs' := Array.mergeSplit splitIds argFuns otherArgs
      let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
      let ruleProof ← instantiateMVars (← mkLambdaFVars fvars proof)
      let ruleName := constName.append argName |>.append "revCDeriv_rule"
      trace[Meta.generate_ftrans] "revCDeriv rule {ruleName}\n{← ppExpr (← inferType ruleProof)}"

      if (← inferType ruleProof).hasMVar then
        throwError "rule has meta variables\n{← ppExpr (← inferType ruleProof)}"

      if ruleProof.hasMVar then
        throwError "rule proof has meta variables\n{← ppExpr ruleProof}"

      let ruleInfo : TheoremVal := 
      {
        name  := ruleName
        type  := ← instantiateMVars (← inferType ruleProof)
        value := ruleProof
        levelParams := vLvlName :: info.levelParams
      }

      addDecl (.thmDecl ruleInfo)

      withLetDecls argNames transArgFuns fun transArgFunLets => do

        let xs' := Array.mergeSplit splitIds transArgFunLets otherArgs
        let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
        let rhs ← 
          mkLambdaFVars 
            ((#[w] : Array Expr) ++ transArgFunLets) 
            (← mkAppOptM transFunName (fvars.map .some))

        let xs' := Array.mergeSplit splitIds argFuns otherArgs
        let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
        let ruleDef ← instantiateMVars (← mkForallFVars fvars (← mkEq lhs rhs))
        let ruleDefName := constName.append argName |>.append "revCDeriv_rule_def"
        trace[Meta.generate_ftrans] "revCDeriv def rule {ruleDefName}\n{← ppExpr ruleDef}"

        let ruleDefInfo : TheoremVal := 
        {
          name  := ruleDefName
          type  := ruleDef
          value := ruleProof
          levelParams := vLvlName :: info.levelParams
        }

        addDecl (.thmDecl ruleDefInfo)



def generateRevCDeriv' (constName : Name) (mainNames trailingNames : Array Name) (conv : TSyntax `conv) : TermElabM Unit := do
  let info ← getConstInfoDefn constName

  forallTelescope info.type fun xs type => do

    let (orgCtx, args) ← splitToCtxAndArgs xs

    let .some ⟨_u,K,_isROrC⟩ ← getFieldOutOfContextQ xs
      | throwError "unable to figure out what is the field"

    trace[Meta.generate_ftrans] "detected field {← ppExpr K}"

    let (mainArgs, unusedArgs, trailingArgs, argKinds) 
      ← splitArgs args mainNames trailingNames

    -- ensure that `mainNames` are in the right order
    let mainNames ← mainArgs.mapM (fun arg => arg.fvarId!.getUserName)

    let types := (← liftM <| mainArgs.mapM inferType).push type
    extendContext K types fun ctx' => do

    trace[Meta.generate_ftrans] "extending context with {← liftM <| ctx'.mapM fun c => do pure s!"({← ppExpr c} : {← ppExpr (← inferType c)})"}"
    
    let ctx := orgCtx ++ ctx'

    trace[Meta.generate_ftrans] "generating revCDeriv for {constName} in arguments {← mainArgs.mapM fun arg => do pure s!"({←ppExpr arg} : {← ppExpr (← inferType arg)})"}"

    checkNoDependentTypes mainArgs xs

    let vLvlName := mkUnusedName info.levelParams `w
    -- let v ← mkFreshLevelMVar
    let v := Level.param vLvlName
    withLocalDeclQ `W .implicit q(Type $v) fun W => do
    withLocalDecl `instW .instImplicit (← mkAppM ``SemiInnerProductSpace #[K,W]) fun instW => do
    withLocalDeclQ (u:=v) `w .default W fun w => do

    let ctx := ctx ++ (#[W,instW] : Array Expr)

    -- argFuns are selected arguments parametrized by `W`
    let argFunDecls :=
      mkLocalDecls mainNames .default (← args.mapM fun arg => do mkArrow W (← inferType arg))

    withLocalDecls argFunDecls fun argFuns => do

      let argFunApps := argFuns.map (fun argFun => argFun.app w)

      let lhs ← 
        withLetDecls mainNames argFunApps fun args' => do
          let xs' := orgCtx ++ mergeArgs args' unusedArgs trailingArgs argKinds
          let f ← mkLambdaFVars ((#[w] : Array Expr) ++ trailingArgs ++ args') (← mkAppOptM constName (xs'.map Option.some))
          mkAppM ``revCDeriv #[K,f]

      trace[Meta.generate_ftrans] "lhs for revCDeriv rule\n{← ppExpr lhs}"

      -- let argFunPropDecls ← 
      --   argFuns.mapM (fun argFun => do
      --     let name := (← argFun.fvarId!.getUserName).appendBefore "h"
      --     let bi : BinderInfo := .default
      --     let type ← mkAppM ``HasAdjDiff #[K,argFun]
      --     pure (name, bi, fun _ : Array Expr => pure (f:=TermElabM) type))

      -- withLocalDecls argFunPropDecls fun argFunProps => do

      -- let (rhs, proof) ← elabConvRewrite lhs conv

      -- trace[Meta.generate_ftrans] "rhs for revCDeriv rule\n{← ppExpr rhs}"

      -- let .lam _ _ b _ := rhs
      --   | throwError "transformed function should be in the form `fun w => ...` but got\n{← ppExpr rhs}"

      -- let b := b.instantiate1 w

      -- let transArgFuns ← argFuns.mapM (fun argFun => mkAppM ``revCDeriv #[K, argFun, w])

      -- let transArgNames := argNames.map (fun n => n.appendAfter "d" |>.appendAfter (toString n))
      -- let transArgFunDecls := 
      --   mkLocalDecls transArgNames .default (← liftM <| transArgFuns.mapM inferType)

      -- withLocalDecls transArgFunDecls fun transArgFunVars => do

      -- -- find all occurances of `<∂ (w':=w), argFunᵢ w` and replace it with recently introduced fvar
      -- let b' ← eliminateTransArgFun b argFuns transArgFuns transArgFunVars
      -- if b'.containsFVar w.fvarId! then
      --   throwError s!"transformed function {← ppExpr b'} still contains {← ppExpr w}"

      -- let idx ← firstExplicitNonTypeIdx xs

      -- let xs' := Array.mergeSplit splitIds transArgFunVars otherArgs
      -- let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
      -- let transFun ← instantiateMVars (← mkLambdaFVars fvars b')
      -- let transFunName := constName.append argName |>.append "revCDeriv"
      -- trace[Meta.generate_ftrans] "generated revCDeriv function {transFunName}\n{← ppExpr transFun}"

      -- let transFunInfo : DefinitionVal := 
      -- {
      --   name  := transFunName
      --   type  := (← inferType transFun)
      --   value := transFun
      --   hints := .regular 0
      --   safety := .safe
      --   levelParams := vLvlName :: info.levelParams
      -- }

      -- addAndCompile (.defnDecl transFunInfo)

      -- let xs' := Array.mergeSplit splitIds argFuns otherArgs
      -- let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
      -- let ruleProof ← instantiateMVars (← mkLambdaFVars fvars proof)
      -- let ruleName := constName.append argName |>.append "revCDeriv_rule"
      -- trace[Meta.generate_ftrans] "revCDeriv rule {ruleName}\n{← ppExpr (← inferType ruleProof)}"

      -- if (← inferType ruleProof).hasMVar then
      --   throwError "rule has meta variables\n{← ppExpr (← inferType ruleProof)}"

      -- if ruleProof.hasMVar then
      --   throwError "rule proof has meta variables\n{← ppExpr ruleProof}"

      -- let ruleInfo : TheoremVal := 
      -- {
      --   name  := ruleName
      --   type  := ← instantiateMVars (← inferType ruleProof)
      --   value := ruleProof
      --   levelParams := vLvlName :: info.levelParams
      -- }

      -- addDecl (.thmDecl ruleInfo)

      -- withLetDecls argNames transArgFuns fun transArgFunLets => do

      --   let xs' := Array.mergeSplit splitIds transArgFunLets otherArgs
      --   let fvars := xs'[0:idx] ++ (#[W,instW] : Array Expr) ++ xs'[idx:]
      --   let rhs ← 
      --     mkLambdaFVars 
      --       ((#[w] : Array Expr) ++ transArgFunLets) 
      --       (← mkAppOptM transFunName (fvars.map .some))

      --   let xs' := Array.mergeSplit splitIds argFuns otherArgs
      --   let fvars := xs'[0:idx] ++ (#[W, instW] : Array Expr) ++ xs'[idx:] ++ argFunProps
      --   let ruleDef ← instantiateMVars (← mkForallFVars fvars (← mkEq lhs rhs))
      --   let ruleDefName := constName.append argName |>.append "revCDeriv_rule_def"
      --   trace[Meta.generate_ftrans] "revCDeriv def rule {ruleDefName}\n{← ppExpr ruleDef}"

      --   let ruleDefInfo : TheoremVal := 
      --   {
      --     name  := ruleDefName
      --     type  := ruleDef
      --     value := ruleProof
      --     levelParams := vLvlName :: info.levelParams
      --   }

      --   addDecl (.thmDecl ruleDefInfo)


open Lean.Parser.Tactic.Conv in
syntax "#generate_revCDeriv" term num* " by " convSeq : command

elab_rules : command
| `(#generate_revCDeriv $fnStx $argIds:num* by $rw:convSeq) => do
  Command.liftTermElabM do
    let a := argIds.map (fun a => a.getNat)
    let fn ← elabTerm fnStx none
    let .some constName := fn.getAppFn'.constName?
      | throwError "unknown function {fnStx}"
    generateRevCDeriv constName a.toArraySet (← `(conv| ($rw)))



variable 
  {K : Type u} [RealScalar K]
  {ι : Type v} {κ : Type v'} [EnumType ι] [EnumType κ]

def matmul  (A : ι → κ → K) (x : κ → K) (i : ι) : K := ∑ j, A i j * x j

set_option pp.universes true

set_option trace.Meta.generate_ftrans true
#eval show TermElabM Unit from do

  generateRevCDeriv' ``matmul #[`A,`x] #[`i] (← `(conv| (unfold matmul; autodiff)))
