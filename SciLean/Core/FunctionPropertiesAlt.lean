import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

import SciLean.Data.ArraySet

namespace SciLean

open Lean Parser.Term Lean.Elab Meta

--------------------------------------------------------------------------------
-- isSmooth
--------------------------------------------------------------------------------

@[inline]
def _root_.Array.partitionIdxM {m} [Monad m] (p : α → m Bool) (as : Array α) : m (Array α × Array α × Array (Sum Nat Nat)) := do
  let mut bs := #[]
  let mut cs := #[]
  let mut ids : Array (Sum Nat Nat) := #[]
  let mut i := 0
  let mut j := 0
  for a in as do
    if ← p a then
      bs := bs.push a
      ids := ids.push (.inl i)
      i := i + 1
    else
      cs := cs.push a
      ids := ids.push (.inr j)
      j := j + 1
  return (bs, cs, ids)

def _root_.Array.merge (ids : Array (Sum Nat Nat)) (bs cs : Array α) [Inhabited α] : Array α :=
  ids.map λ id => 
    match id with
    | .inl i => bs[i]!
    | .inr j => cs[j]!

variable [MonadControlT MetaM n] [Monad n]

#check map2MetaM

@[inline] def map4MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → δ → ε → MetaM α) → MetaM α) {α} (k : β → γ → δ → ε → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d e => runInBase <| k b c d e)

private def createCompositionImpl (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → MetaM α) : MetaM α := do
  withLocalDecl `T .implicit (mkSort levelOne) λ T => do
    withLocalDecl `t .default T λ t => do
      
      let xIds := xs.map λ x => x.fvarId!

      let mut lctx ← getLCtx
      let mut i := lctx.numIndices
      let mut ys : Array Expr := .mkEmpty xs.size
      for id in xIds do 
        let name ← id.getUserName
        let bi ← id.getBinderInfo 
        let type ← mkArrow T (← id.getType)
        let yId ← mkFreshFVarId
        ys := ys.push (mkFVar yId)
        lctx := lctx.addDecl (mkLocalDeclEx i yId name type bi)
        i := i + 1

      withLCtx lctx (← getLocalInstances) do
        let yts ← ys.mapM λ y => mkAppM' y #[t]
        let replacePairs := xIds.zip yts
        let e' := replacePairs.foldl (init:=e) λ e (id,yt) => e.replaceFVarId id yt

        k T t ys e'

      -- This does not work because `witlLocalDecls` requires Inhabited and that breaks map4MetaM
      -- let yDecls ← xIds.mapM λ id => do
      --   let name ← id.getUserName
      --   let bi ← id.getBinderInfo 
      --   let type ← mkArrow T (← id.getType)
      --   pure (name, bi, λ _ => pure type)

      -- withLocalDecls yDecls λ ys => do
      --   let yts ← ys.mapM λ y => mkAppM' y #[t]
      --   let replacePairs := xIds.zip yts
      --   let e' := replacePairs.foldl (init:=e) λ e (id,yt) => e.replaceFVarId id yt

      --   k T t ys e'
          

/-- 
  For every free variable `x : X` introduce `y : T → X` and replace every `x` in `e` with `y t`.

  Then call `k` on `e` providing the newly introduces `T`, `t`, `ys`
  -/
def createComposition  (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → n α) : n α := 
  map4MetaM (fun k => createCompositionImpl e xs k) k


/-- 
  Takes an expression `e` and every free variable `x : X`, specified by `xs`, is replaced by `y t` where `y : T → X`, `t : T` where `t` and `T` are new free variables.

  Returns:
    1. modified expression `e`
    2. array of free variables [T, t, x₁, ..., xₙ] where [x₁, ..., xₙ] are replacenmens for the specified free variables
    3. local contex after modification
    4. local instances after modification
  
  -/
def createComposition' (e : Expr) (fvars : Array FVarId) (lctx : LocalContext) (localInsts : LocalInstances) 
  : MetaM (Expr × Array FVarId × LocalContext × LocalInstances) := 
do
  withLCtx lctx localInsts do
    withLocalDecl `T .implicit (mkSort levelOne) λ T => do
      withLocalDecl `t .default T λ t => do

        -- check we can actually do it
        lctx.forM λ decl => 
          fvars.forM λ fvar => do
            if decl.type.containsFVar fvar then
              throwError "Failed `createComposition`, free variable {← fvar.getUserName} appears in type of {decl.userName}! Dependent types are not supported!"
            if let .some val := decl.value? then
              if val.containsFVar fvar then
                throwError "Failed `createComposition`, free variable {← fvar.getUserName} appears in the value of {decl.userName}! This is currently not supported!"
        
        let localDecls ← fvars.mapM λ id => do
          let name ← id.getUserName
          let bi ← id.getBinderInfo 
          let type ← mkArrow T (← id.getType)
          pure (name, bi, λ _ => pure type)

        withLocalDecls localDecls λ ys => do
          let yts ← ys.mapM λ y => mkAppM' y #[t]
          let replacePairs := fvars.zip yts
          let e := replacePairs.foldl (init:=e) λ e (id,yt) => e.replaceFVarId id yt

          let newFVars := (#[T,t].append ys).map λ y => y.fvarId!
      
          -- TODO: Maybe return context without the old free variables
          pure (e, newFVars, ← getLCtx, ← getLocalInstances)
          

/-- Makes a type that says that `e` is smooth in the given free variables
  
  Returns expression `e [x₀ -> y₁ t, ... xₙ -> y₁ t]
  -/
def createIsSmooth (e : Expr) (abstractOver : Array Expr) (smoothArgIds : ArraySet Nat) : MetaM Expr := do

  let args := e.getAppArgs

  let smoothArgs := smoothArgIds.data.map λ i => args[i]!

  createComposition e smoothArgs λ T t ys e => do 
    -- replace smooth arguments with new values from `ys`
    let abstractOver := abstractOver.map λ arg => 
      if let .some i := smoothArgs.findIdx? (λ sarg => sarg == arg) then
        ys[i]!
      else
        arg

    withLocalDecl `inst .instImplicit (← mkAppM ``Vec #[T]) λ VecT => do

      let smoothDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM ``IsSmooth #[y]
        pure (name, bi, λ _ => pure type)
  
      withLocalDecls smoothDecls λ smoothYs => do
        let vars := #[T,VecT] 
          |>.append abstractOver
          |>.append smoothYs
        let statement ← mkAppM ``IsSmooth #[← mkLambdaFVars #[t] e]
        mkLambdaFVars vars statement

      

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth

syntax "isSmooth" bracketedBinder* (":=" term)? : argProp

#check Command.liftCoreM
#check TermElabM

set_option linter.unusedVariables false 

#check TheoremVal.mk

elab_rules : command
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? argument $arg:argSpec isSmooth $extraAssumptions:bracketedBinder* $[:= $proof:term]?) => do

  let data ← Command.liftTermElabM <| liftMacroM <| FunctionPropertyData.parse id parms retType arg

  let mainArgNames := data.mainArgIds.map (λ i => data.argName! i)

  Command.liftTermElabM  do
    let funStx ← liftMacroM do
      let data ← FunctionPropertyData.parse id parms retType arg
      let funBinders ← data.binders.mapM (λ b => b.toFunBinder)
      let args := data.binders.filterMap (λ b => if b.isExplicit then some b.getIdent else none)
      dbg_trace  s!"args: {args.map λ arg => arg.raw.prettyPrint}"

      `(λ $funBinders* => $id $args*)

    IO.println s!"funStx {funStx.raw.prettyPrint}"
    let function ← Term.elabTerm funStx none

    IO.println s!"Function {← ppExpr function} : {← ppExpr (← inferType function)}"
  
    Term.elabBinders parms λ xs => do
      IO.println s!"Elaborated binders: {← xs.mapM λ x => do pure s!"{← x.fvarId!.getUserName} {repr (← x.fvarId!.getBinderInfo)} {← ppExpr (← x.fvarId!.getType)}" }"

    lambdaTelescope function λ xs b => do

      let smoothness ← createIsSmooth b xs #[4,5].toArraySet
      IO.println s!"Nicelly generated smoothness statnment: {← ppExpr smoothness}"

      let smoothness ← createIsSmooth b xs #[4].toArraySet
      IO.println s!"Nicelly generated smoothness statnment: {← ppExpr smoothness}"

      let smoothness ← createIsSmooth b xs #[5].toArraySet
      IO.println s!"Nicelly generated smoothness statnment: {← ppExpr smoothness}"

      let xName := `x

      let ys ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return false else return true)
      let x ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return true else return false)
      
      let f' ← mkLambdaFVars ys (← mkAppM ``IsSmooth #[← mkLambdaFVars x b])
      IO.println s!"smoothness in x: {← ppExpr f'}"


    lambdaTelescope function λ xs b => do

      let xName := `x

      let ys ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return false else return true)
      let x ← xs.filterM (λ x => do  if (←x.fvarId!.getUserName)==xName then return true else return false)

      let f' ← mkLambdaFVars ys (← mkAppM ``IsSmooth #[← mkLambdaFVars x b])
      IO.println s!"smoothness in x: {← ppExpr f'}"


    let smoothness ← 
    withLocalDecl `T .implicit (mkSort levelOne)               λ T => do
      withLocalDecl "inst✝" .instImplicit (← mkAppM ``Vec #[T]) λ TVec => do
        withLocalDecl `t .default T                                λ t => do
          lambdaTelescope function λ xs b => do

            let mainArgTest := λ arg : Expr => do 
              let name ← arg.fvarId!.getUserName
              if (mainArgNames.find? (λ name' => name' == name)).isSome then -- 
                return true
              else 
                return false

            let (mainArgs, contextArgs, ids) ← xs.partitionIdxM mainArgTest

            -- IO.println s!"main args: {← mainArgs.mapM (λ arg => ppExpr arg)}"

            let mainArgsDecls ← mainArgs.mapM λ arg => do
              let name ← arg.fvarId!.getUserName
              let bi := BinderInfo.default
              let type ← mkArrow T (← inferType arg)
              pure (name, bi, λ (_:Array Expr) => (pure type : TermElabM Expr))

            withLocalDecls mainArgsDecls λ xs => do

              let isSmoothDecls ← xs.mapM (λ x => do
                let name : Name := "inst✝"
                let bi := BinderInfo.instImplicit
                let type ← mkAppM ``IsSmooth #[x]
                return (name, bi, λ (_:Array Expr) => (pure type : TermElabM Expr)))

              withLocalDecls isSmoothDecls λ smoothArgs => do
                let xts ← xs.mapM (λ xt => mkAppM' xt #[t])
                let replacePairs := mainArgs.zip xts
                let b' := replacePairs.foldl (init := b)
                            λ b (x,xt) => b.replace (λ x' => if x==x' then some xt else none)
                let f ← liftMetaM <|
                  (mkLambdaFVars #[t] b' 
                  >>= λ x => mkAppM ``IsSmooth #[x] 
                  >>= mkForallFVars smoothArgs
                  >>= mkForallFVars (ids.merge xs contextArgs)
                  >>= mkForallFVars #[T,TVec])

                IO.println s!"smoothness in x and y: {← ppExpr f}"
                pure f


    -- get rid of some universe metavariables
    let smoothness ← instantiateMVars smoothness
    let prf ← 
      forallTelescope smoothness λ xs b => do
        let val ← Term.elabTermAndSynthesize proof.get! b 
        mkLambdaFVars xs val


    let info : TheoremVal :=
    {
      name := id.getId.append ((`arg_).appendAfter data.mainArgString) |>.append `isSmooth
      type := smoothness
      value := prf
      levelParams := []
    }

    addDecl (.thmDecl info)
    addInstance info.name .local 1000
  
  IO.println "hihi"


-- For a give function/constant property and arguments this gives you the name of the theorem talking about the property in those arguments
structure FunctionTheorem where
  thrm : Name

-- extraPreArgNum : Nata
-- extraPostArgNum : Nat

-- Retrieve theorem for a give function/constant, function transform/property and set of arguments indices 
-- For example `HAdd.hAdd` has 6 arguments `{X Y Z} [HAdd X Y Z] x y`
-- and it has differential, IsSmooth in [4,5] and [4] and [5]
-- but is IsLin, adjoint only in [4,5]
def FunctionTheorems : PersistentHashMap (Name × Name) (PersistentHashMap (ArraySet Nat) FunctionTheorem) := sorry

def getFunctionTheorem (constName : Name) (transOrPropName : Name) (fvar : FVarId) (args : Array Expr) : Option Expr := sorry

set_option pp.funBinderTypes true in
function_properties HAdd.hAdd {X : Type} [Vec X]  (x y : X) : X
argument (x,y)
  isSmooth := by admit
argument x
  isSmooth := by admit
argument y
  isSmooth := by admit

#check HAdd.hAdd.arg_xy.isSmooth
#check HAdd.hAdd.arg_x.isSmooth
#check HAdd.hAdd.arg_y.isSmooth

instance {X} [Vec X] : IsSmooth (λ x : X => x) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ y : Y => x) := sorry

example : IsSmooth λ x : ℝ => x + x := by infer_instance

example (y : ℝ) : IsSmooth λ x : ℝ => x + y := by infer_instance

set_option trace.Meta.synthInstance true in
example (y : ℝ) : IsSmooth λ x : ℝ => y + x := by apply HAdd.hAdd.arg_y.isSmooth


#eval show MetaM Unit from do 
  let info ← getConstInfo ``HAdd.hAdd
  let type := info.type

  forallTelescope type λ xs b => do
    let mut lctx ← getLCtx
    let insts ← getLocalInstances
    lctx := Prod.fst <| xs.foldl (init := (lctx,0)) λ (lctx,i) x =>
      let xId := x.fvarId!
      let name := (lctx.get! xId).userName
      if name.isInternal then
        let name := name.modifyBase λ n => n.appendAfter (toString i)
        (lctx.setUserName xId name, i+1)
      else
        (lctx,i+1)    

    withLCtx lctx (← getLocalInstances) do
      let names ← xs.mapM λ x => x.fvarId!.getUserName
      IO.println s!"Argument names: {names}"
      IO.println s!"Internal names: {names.map λ name => name.isInternal}"
      IO.println s!"Impl detail names: {names.map λ name => name.isImplementationDetail}"



  -- withLCtx lctx localInsts do
  --   lctx.modifyLocalDecl
  --   let newDecls ← fvars.mapM λ fvar

  -- let instanceId := mkIdent $ data.funPropNamespace.append "isSmooth"

  -- let (instanceType, extraBinders) ← 
  --   match data.mainArgNum with 
  --   | 0 => Macro.throwError "Must specify at least one argument!" 
  --   | 1 => pure (← `(IsSmooth  $(← data.mkLambda)), (#[] : Array BracketedBinder))
  --   | _ => do 
  --     let (T, mainBinders, lambda) ← data.mkCompositionLambda
  --     let TBinders : Array BracketedBinder :=  #[← `(bracketedBinderF| {$T : Type _}), ← `(bracketedBinderF| [Vec $T])]
  --     let mainAssumptions ← mainBinders.mapM (β := BracketedBinder) (λ b => `(bracketedBinderF| [IsSmooth $b.getIdent] ))
  --     let instType ← `(IsSmooth $lambda)
  --     pure (instType, TBinders.append (mainBinders.append mainAssumptions))

  -- let proof ← 
  --   match proof with
  --   | none => `(term| by first | apply isLin_isSmooth | infer_instance | (unfold $id; infer_instance); done)
  --   | some prf =>pure  prf

  -- let finalCommand ←
  --     `(@[fun_prop] theorem $instanceId $data.contextBinders* $extraBinders* $extraAssumptions* : $instanceType := $proof)
  
  -- return finalCommand 


