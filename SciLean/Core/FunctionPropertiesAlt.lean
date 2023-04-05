import SciLean.Core.Attributes
import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty
import SciLean.Core.Meta.RewriteBy

import SciLean.Tactic.AutoDiff

import SciLean.Data.ArraySet

import SciLean.Core.FunctionTheorems

namespace SciLean

set_option linter.unusedVariables false 

open Lean Parser.Term Lean.Elab Meta


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

@[inline] def _root_.Lean.Meta.map3MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → δ → MetaM α) → MetaM α) {α} (k : β → γ → δ → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d => runInBase <| k b c d)

@[inline] def _root_.Lean.Meta.map4MetaM [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → δ → ε → MetaM α) → MetaM α) {α} (k : β → γ → δ → ε → m α) : m α :=
  controlAt MetaM fun runInBase => f (fun b c d e => runInBase <| k b c d e)

private def createCompositionImpl (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → MetaM α) : MetaM α := do
  withLocalDecl `T .implicit (mkSort levelOne) λ T => do
    withLocalDecl `t .default T λ t => do
      
      let xIds := xs.map λ x => x.fvarId!

      -- We are not using `withLocalDecls` as it requires `Inhabited α` and that 
      -- does not play well with map4MetaM
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

/-- 
  For every free variable `x : X` introduce `y : T → X` and replace every `x` in `e` with `y t`.

  Then call `k` on `e` providing the newly introduces `T`, `t`, `ys`
  -/
def createComposition  (e : Expr) (xs : Array Expr) (k : (T : Expr) → (t : Expr) → (ys : Array Expr) → (e' : Expr) → n α) : n α := 
  map4MetaM (fun k => createCompositionImpl e xs k) k


-- def createCompositionOtherImpl (e : Expr) (xs : Array Expr) (other : Array Expr) 
--   (k : (T : Expr) → (t : Expr) →  (ys : Array Expr) → (other' : Array Expr) → (e' : Expr) → MetaM α) : MetaM α := do

/-- 
  For every free variable `x : X`, elements of `xs`, introduce `y : T → X`, elements of `ys`, and: 
    - replace every `x` in `e` with `y t` 
    - replace every `x` in `other` with `y`.
  where `{T : Type} (t : T)` are newly introduced free variables

  Then call `k` on `e` providing `T`, `t`, `ys` `other`

  NOTE: Most likely this operation makes sense only if `other` is a list of free variables
  -/
def createCompositionOther (e : Expr) (xs : Array Expr) (other : Array Expr) 
  (k : (T : Expr) → (t : Expr) →  (ys : Array Expr) → (other' : Array Expr) → (e' : Expr) → n α) : n α := do

  createComposition e xs λ T t ys e => do 
    
    let other := other.map λ e' => 
      e'.replace (λ e'' => Id.run do
        for (x, y) in xs.zip ys do
          if e'' == x then 
            return some y
        return none)

    k T t ys other e

/-- 
Applies `funName` to `e` but as a composition through arguments specified by `argIds`

This means, for `e = f x₁ .. xₙ` return expression `λ {T} [Space T] a₁ ... aₘ [FunProp xᵢ] : Fun λ t => f x₁ .. (xᵢ t) xₙ` 

where:
  - `Fun`, `FunProp`, `Space` correspond to `funName`, `propName`, `spaceName`
  - `i ∈ argIds`
  - `a₁, ..., aₘ ∈ abstractOver` but any occurance of `xᵢ : X` is replaced with `xᵢ : T → X` 
For example:
```
createFunProp ``differential ``IsSmooth ``Vec (@HAdd.hAdd X X X inst.toHAdd x y) #[4] #[X, inst, x, y]
```
produces
```
∀ {T : Type} [Vec T] {X} [inst : Vec X] (x : X) (y : T → X) [IsSmooth y] : differential λ t => x + (y t)
```
-/
def mkCompositionFunApp (funName propName spaceName : Name) (e : Expr) (argIds : ArraySet Nat) (abstractOver : Array Expr) : MetaM Expr := do

  let args := e.getAppArgs

  let xs := argIds.data.map λ i => args[i]!

  createCompositionOther e xs abstractOver λ T t ys abstractOver e => do

    withLocalDecl `inst .instImplicit (← mkAppM spaceName #[T]) λ SpaceT => do

      let funPropDecls ← ys.mapM λ y => do
        let name := `inst
        let bi := BinderInfo.instImplicit
        let type ← mkAppM propName #[y]
        pure (name, bi, λ _ => pure type)
  
      withLocalDecls funPropDecls λ ysProp => do
        let vars := #[T,SpaceT]
          |>.append abstractOver
          |>.append ysProp
        let statement ← mkAppM funName #[← mkLambdaFVars #[t] e]
        mkForallFVars vars statement

/-- Makes a type that says that `f x₁ .. xₙ` satisfies function propsotion `propName` in `xᵢ`
  
  The returned expression is: `∀ a₁ ... aₘ : FunProp λ xᵢ => f x₁ .. xᵢ xₙ` 
  where `a₁, ..., aₘ ∈ abstractOver` -/
def mkSingleArgFunApp (funName : Name) (e : Expr) (i : Nat) (abstractOver : Array Expr) : MetaM Expr := do

  let args := e.getAppArgs

  let xi := args[i]!

  let statement ← mkAppM funName #[← mkLambdaFVars #[xi] e]

  let abstractOver := abstractOver.filter (λ a => a != xi)

  mkForallFVars abstractOver statement


/--
  Creates argument suffix for a constant and specified arguments.

  Examples:

    For `constName = ``foo` where `foo : ∀ (α : Type) → [inst : Add α] → (x y : α) → α`
    and `argIds = #[2,3]`
    returns `xy` because the third argument has name `x` and the fourth argument has name `y`

    For `HAdd.hAdd : ∀ (α β γ : Type) → [inst : HAdd α β γ] → α → β → γ`
    and `argIds = #[4,5]`
    returns `a4a5` beause fifth and sixth arguments are anonymous
  -/
def constArgSuffix (constName : Name) (argIds : ArraySet Nat) : MetaM String := do

  let info ← getConstInfo constName
  let suffix ← forallTelescope info.type λ args _ => do
    IO.println s!"{← (args.mapM λ arg => ppExpr arg)}"
    (argIds.data.mapM λ i => do
      let name ← args[i]!.fvarId!.getUserName
      IO.println s!"{← ppExpr args[i]!}"
      if name.isInternal then
        return name.eraseMacroScopes.appendAfter (toString i)
      else
        return name)

  return suffix.foldl (init:="") λ s n => s ++ toString n             


#check TSyntax
def _root_.Lean.TSyntax.argSpecNames (argSpec : TSyntax ``argSpec) : Array Name := 
  match argSpec with 
  | `(argSpec| $id:ident) => #[id.getId]
  | `(argSpec| ($id:ident, $ids:ident,*)) => #[id.getId].append (ids.getElems.map λ id => id.getId)
  | _ => #[]

syntax "funProp" ident ident bracketedBinder* ":=" term : argProp
syntax "funTrans" ident ident ident bracketedBinder* ":=" term "by" term: argProp

elab_rules : command
| `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $propId $spaceId $assumptions2* := $proof) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ xs => do

      let propName := propId.getId
      let spaceName := spaceId.getId
  
      let argNames : Array Name := argSpec.argSpecNames 

      let explicitArgs := (← xs.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
      let e ← mkAppM id.getId explicitArgs
      let args := e.getAppArgs

      let mainArgIds ← argNames.mapM λ name => do
        let idx? ← args.findIdxM? (λ arg => do
          if let .some fvar := arg.fvarId? then
            let name' ← fvar.getUserName
            pure (name' == name)
          else 
            pure false)
        match idx? with
        | some idx => pure idx
        | none => throwError "Specified argument `{name}` is not valid!"

      let mainArgIds := mainArgIds.toArraySet

      let theoremType ← mkCompositionFunApp propName propName spaceName e mainArgIds xs >>= instantiateMVars

      let prf ← forallTelescope theoremType λ ys b => do
        let val ← Term.elabTermAndSynthesize proof b 
        mkLambdaFVars ys val

      let theoremName := id.getId
        |>.append `arg_
        |>.appendAfter (← constArgSuffix id.getId mainArgIds)
        |>.append propName.getString

      let info : TheoremVal :=
      {
        name := theoremName
        type := theoremType
        value := prf
        levelParams := []
      }

      addDecl (.thmDecl info)
      addInstance info.name .local 1000

      addFunctionTheorem id.getId propName mainArgIds ⟨theoremName⟩

      -- For only one main argument we also formulate the theorem in non-compositional manner
      -- For example this formulates
      --   `IsSmooth λ x => x + y`
      -- in addition to 
      --   `IsSmooth λ t => (x t) + y` 
      if mainArgIds.size = 1 then
        let i := mainArgIds.data[0]!
        let theoremType ← mkSingleArgFunApp propName e i xs >>= instantiateMVars
        
        let prf ← forallTelescope theoremType λ xs b => do
          let thrm : Ident := mkIdent theoremName
          let prf ← Term.elabTermAndSynthesize (← `(by apply $thrm)) b
          mkLambdaFVars xs prf

        let info : TheoremVal :=
        {
          name := theoremName.appendAfter "'"
          type := theoremType
          value := prf
          levelParams := []
        }

        addDecl (.thmDecl info)
        addInstance info.name .local 1000

| `(function_property $id $parms* $[: $retType]? 
    argument $argSpec $assumptions1*
    funTrans $transId $propId $spaceId $assumptions2* := $Tf by $proof) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ xs => do

      let transName := transId.getId
      let propName := propId.getId
      let spaceName := spaceId.getId
  
      let argNames : Array Name := argSpec.argSpecNames 

      let explicitArgs := (← xs.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
      let e ← mkAppM id.getId explicitArgs
      let args := e.getAppArgs

      let mainArgIds ← argNames.mapM λ name => do
        let idx? ← args.findIdxM? (λ arg => do
          if let .some fvar := arg.fvarId? then
            let name' ← fvar.getUserName
            pure (name' == name)
          else 
            pure false)
        match idx? with
        | some idx => pure idx
        | none => throwError "Specified argument `{name}` is not valid!"

      let mainArgIds := mainArgIds.toArraySet

      let funTrans ← mkCompositionFunApp transName propName spaceName e mainArgIds xs >>= instantiateMVars

      forallTelescope funTrans λ ys b => do

        let Tf  ← Term.elabTermAndSynthesize Tf (← inferType b)
        let theoremType ← mkEq b Tf
        let prf ← Term.elabTermAndSynthesize proof theoremType

        let theoremName := id.getId
          |>.append "arg_"
          |>.appendAfter (← constArgSuffix id.getId mainArgIds)
          |>.append transName.getString
          |>.appendAfter "_simp"

        let info : TheoremVal :=
        {
          name := theoremName
          type := ← mkForallFVars ys theoremType
          value := ← mkLambdaFVars ys prf
          levelParams := []
        }

        addDecl (.thmDecl info)

        addFunctionTheorem id.getId transName mainArgIds ⟨theoremName⟩



 
instance {X} [Vec X] : IsSmooth (λ x : X => x) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ y : Y => x) := sorry

instance {X} [SemiHilbert X] : HasAdjDiff (λ x : X => x) := sorry
instance {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X): HasAdjDiff (λ y : Y => x) := sorry

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth
theorem hasAdjoint_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsLin f] : HasAdjoint f := sorry
theorem hasAdjDiff_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsSmooth f] : HasAdjDiff f := sorry

syntax " IsSmooth " bracketedBinder* (":=" term)? : argProp
syntax " IsLin " bracketedBinder* (":=" term)? : argProp
syntax " HasAdjoint " bracketedBinder* (":=" term)? : argProp
syntax " HasAdjDiff " bracketedBinder* (":=" term)? : argProp

-- For some reason macro turning just `isSmooth := proof` into `funProp IsSmooth Vec := proof` does not work
macro_rules
-- IsSmooth
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec $assumptions1*
    IsSmooth $assumptions2* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsSmooth
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $prop $space $assumptions2* := $prf)
-- IsLin
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    IsLin $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsLin
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)
-- HasAdjoint
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjoint $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjoint
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)
-- HasAdjDiff
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjDiff $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjDiff
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


function_properties HAdd.hAdd {X : Type} (x y : X) : X
argument (x,y) [Vec X]
  IsLin    := sorry,
  IsSmooth := sorry,
  funTrans SciLean.differential SciLean.IsSmooth SciLean.Vec [Vec X] := λ t dt => ∂ x t dt + ∂ y t dt by (by funext t dt; simp; admit)
argument (x,y) [SemiHilbert X]
  HasAdjoint := sorry,
  HasAdjDiff := sorry
argument x
  IsSmooth [Vec X],
  HasAdjDiff [SemiHilbert X]
argument y
  IsSmooth [Vec X],
  HasAdjDiff [SemiHilbert X],
  funTrans SciLean.differential SciLean.IsSmooth SciLean.Vec [Vec X] := λ t dt => ∂ y t dt by (by funext t dt; simp; admit)

#eval printFunctionTheorems

example {X} [Vec X] (y : X) : IsSmooth λ x : X => x + y := by infer_instance
example {X} [Vec X] (y : X) : IsSmooth λ x : X => y + x := by infer_instance

#check HAdd.hAdd.arg_a4a5.IsSmooth
#check HAdd.hAdd.arg_a4a5.differential_simp
#check HAdd.hAdd.arg_a4.IsSmooth
#check HAdd.hAdd.arg_a5.IsSmooth'
#check HAdd.hAdd.arg_a5.differential_simp


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


variable (foo : ℝ → ℝ)
#check ∂ foo
