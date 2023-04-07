import SciLean.Core.Defs
import SciLean.Core.Meta.FunctionProperty.Syntax

import SciLean.Lean.Meta.Basic

-- import SciLean.Tactic.AutoDiff

import SciLean.Data.ArraySet

import SciLean.Core.FunctionTheorems

namespace SciLean

set_option linter.unusedVariables false 

open Lean Parser.Term Lean.Elab Meta

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
    (argIds.data.mapM λ i => do
      let name ← args[i]!.fvarId!.getUserName
      if name.isInternal then
        return name.eraseMacroScopes.appendAfter (toString i)
      else
        return name)

  return suffix.joinl toString λ s n => s ++ n


def addFunPropDecl (propName spaceName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) (proofStx : TSyntax `term) : TermElabM Unit := do

  let f    := e.getAppFn
  let args := e.getAppArgs

  let mainArgIds ← xs.mapM (λ x => 
    args.findIdx? (λ arg => arg == x)
    |>.getDM (do throwError s!"Error in `addFunPropDecls`, argument `{← ppExpr x}` has to accur in `{← ppExpr e}!"))

  let mainArgIds := mainArgIds.toArraySet

  let .some (constName, _) := f.const?
    | throwError s!"Error in `addFunPropDecls`, the expression `{← ppExpr e}` has to be an application of a constant!"

  -- normal theorem - in the form `FunProp (uncurryN n λ x₁ .. xₙ => e)`
  let normalTheorem ← mkNormalTheoremFunProp propName e xs contextVars

  let proof ← forallTelescope normalTheorem λ ys b => do
    let val ← Term.elabTermAndSynthesize proofStx b 
    mkLambdaFVars ys val

  let theoremName := constName
    |>.append `arg_
    |>.appendAfter (← constArgSuffix constName mainArgIds)
    |>.append propName.getString

  let info : TheoremVal :=
  {
    name := theoremName
    type := normalTheorem
    value := proof
    levelParams := []
  }

  addDecl (.thmDecl info)
  addInstance info.name .local 1000

  -- composition theorem - in the form `FunProp (λ t => e[xᵢ:=yᵢ t])`
  let compTheorem   ← mkCompTheoremFunProp propName spaceName e xs contextVars

  let compTheoremName := theoremName.appendAfter "'"

  let proof ← forallTelescope compTheorem λ ys b => do
    -- TODO: Fill the proof here!!! 
    -- I think I can manually apply composition rule and then it should be 
    -- automatically discargable by using the normal theorem and product rule
    let val ← Term.elabTermAndSynthesize (← `(by sorry)) b  
    mkLambdaFVars ys val

  let info : TheoremVal :=
  {
    name := compTheoremName
    type := compTheorem
    value := proof
    levelParams := []
  }

  addDecl (.thmDecl info)
  addInstance info.name .local 1000

  addFunctionTheorem constName propName mainArgIds ⟨theoremName, compTheoremName⟩


def addFunTransDecl (transName : Name) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) 
  (defValStx : TSyntax `term) (proof proof2 : TSyntax `Lean.Parser.Tactic.tacticSeq) : TermElabM Unit := do

  let f    := e.getAppFn
  let args := e.getAppArgs

  let mainArgIds ← xs.mapM (λ x => 
    args.findIdx? (λ arg => arg == x)
    |>.getDM (do throwError s!"Error in `addFunPropDecls`, argument `{← ppExpr x}` has to accur in `{← ppExpr e}!"))

  let mainArgIds := mainArgIds.toArraySet

  let .some (constName, _) := f.const?
    | throwError s!"Error in `addFunPropDecls`, the expression `{← ppExpr e}` has to be an application of a constant!"

  -- make definition
  let defType ← inferType (← mkNormalTheoremLhs transName e xs)
  let defVal  ← Term.elabTermAndSynthesize defValStx defType

  let defName := constName
    |>.append "arg_"
    |>.appendAfter (← constArgSuffix constName mainArgIds)
    |>.append transName.getString

  let defValLambda ← do
    let contextVars := maybeFilterContextVars transName xs contextVars
    mkLambdaFVars contextVars defVal >>= instantiateMVars

  let info : DefinitionVal := 
  {
    name := defName
    type := ← inferType defValLambda
    value := defValLambda
    hints := .regular 0
    safety := .safe
    levelParams := []
  }

  addDecl (.defnDecl info)

  let normalTheorem ← mkNormalTheorem transName e xs contextVars defVal

  IO.println s!"Normal theorem for {transName}:\n{← ppExpr normalTheorem}"

  let prf ← forallTelescope normalTheorem λ contextVars statement => do
    let prf ← Term.elabTermAndSynthesize (← `(by $proof:tacticSeq)) statement
    mkLambdaFVars contextVars prf


  let theoremName := defName.appendAfter "_simp"

  let info : TheoremVal :=
  {
    name := theoremName
    type := normalTheorem
    value := prf
    levelParams := []
  }

  addDecl (.thmDecl info)

  let compTheorem ← mkCompTheorem transName e xs contextVars defVal

  IO.println s!"Composition theorem for {transName}:\n{← ppExpr compTheorem}"

  let prf ← forallTelescope compTheorem λ contextVars statement => do
    let prf ← Term.elabTermAndSynthesize (← `(by $proof2)) statement
    mkLambdaFVars contextVars prf

  let compTheoremName := defName.appendAfter "_simp'"

  let info : TheoremVal :=
  {
    name := compTheoremName
    type := compTheorem
    value := prf
    levelParams := []
  }

  addDecl (.thmDecl info)

  addFunctionTheorem constName transName mainArgIds ⟨theoremName,compTheoremName⟩


def _root_.Lean.TSyntax.argSpecNames (argSpec : TSyntax ``argSpec) : Array Name := 
  match argSpec with 
  | `(argSpec| $id:ident) => #[id.getId]
  | `(argSpec| ($id:ident, $ids:ident,*)) => #[id.getId].append (ids.getElems.map λ id => id.getId)
  | _ => #[]

syntax "funProp" ident ident bracketedBinder* ":=" term : argProp
syntax "funTrans" ident bracketedBinder* ":=" term "by" tacticSeq "by" tacticSeq : argProp

elab_rules : command
| `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $propId $spaceId $assumptions2* := $proof) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ contextVars => do

      let propName := propId.getId
      let spaceName := spaceId.getId
  
      let argNames : Array Name := argSpec.argSpecNames 

      let explicitArgs := (← contextVars.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
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

      let xs := mainArgIds.map λ i => args[i]!

      addFunPropDecl propName spaceName e xs contextVars proof

elab_rules : command
| `(function_property $id $parms* $[: $retType]? 
    argument $argSpec $assumptions1*
    funTrans $transId $assumptions2* := $Tf by $proof by $proof2) => do

  Command.liftTermElabM  do

    Term.elabBinders (parms |>.append assumptions1 |>.append assumptions2) λ contextVars => do

      let transName := transId.getId
  
      let argNames : Array Name := argSpec.argSpecNames 

      let explicitArgs := (← contextVars.filterM λ x => do pure (← x.fvarId!.getBinderInfo).isExplicit)
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

      let xs := mainArgIds.map λ i => args[i]!

      addFunTransDecl transName e xs contextVars Tf proof proof2

 
instance {X} [Vec X] : IsSmooth (λ x : X => x) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ y : Y => x) := sorry
instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x  => f (g x)) := sorry
instance {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g] : IsSmooth (λ x  => (f x, g x)) := sorry

instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x  => f (g x)) := sorry
instance {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : X → Y) (g : X → Z) [HasAdjoint f] [HasAdjoint g] : HasAdjoint (λ x  => (f x, g x)) := sorry


instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ xy : X×Y => xy.1) := sorry
instance {X Y} [Vec X] [Vec Y] (x : X): IsSmooth (λ xy : X×Y => xy.2) := sorry

@[simp]
theorem diff_id {X} [Vec X] 
  : ∂ (λ x : X => x) 
    =
    λ x dx => dx := sorry

@[simp]
theorem diff_const {X} [Vec X] (x : X)
  : ∂ (λ y : Y => x) 
    =
    λ y dy => 0 := sorry

@[simp]
theorem diff_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => f (g x)) 
    =
    λ x dx => ∂ f (g x) (∂ g x dx) := sorry

@[simp]
theorem tangentMap_comp {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : Y → Z) (g : X → Y) [IsSmooth f] [IsSmooth g]
  : 𝒯 (λ x => f (g x)) 
    =
    λ x dx => 
      let (y,dy) := 𝒯 g x dx 
      𝒯 f y dy 
  := sorry

@[simp]
theorem adjoint_comp {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : Y → Z) (g : X → Y) [HasAdjoint f] [HasAdjoint g]
  : (λ x => f (g x))†
    =
    λ z => g† (f† z)
  := sorry


@[simp]
theorem diff_prodMk {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g]
  : ∂ (λ x => (f x, g x)) 
    =
    λ x dx => (∂ f x dx, ∂ g x dx) := sorry

@[simp]
theorem tangentMap_prodMk {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z) [IsSmooth f] [IsSmooth g]
  : 𝒯 (λ x => (f x, g x)) 
    =
    λ x dx => 
      let (y,dy) := 𝒯 f x dx
      let (z,dz) := 𝒯 g x dx
      ((y,z), (dy,dz)) := sorry

@[simp]
theorem adjoint_prodMk {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] (f : X → Y) (g : X → Z) [HasAdjoint f] [HasAdjoint g]
  : (λ x => (f x, g x))†
    =
    λ (y,z) => 
      f† y + g† z := sorry


instance {X} [SemiHilbert X] : HasAdjDiff (λ x : X => x) := sorry
instance {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X): HasAdjDiff (λ y : Y => x) := sorry

theorem isLin_isSmooth {X Y} [Vec X] [Vec Y] {f : X → Y} [inst : IsLin f] : IsSmooth f := inst.isSmooth
theorem hasAdjoint_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsLin f] : HasAdjoint f := sorry
theorem hasAdjDiff_on_FinVec {X Y ι κ} {_ : Enumtype ι} {_ : Enumtype κ} [FinVec X ι] [FinVec Y κ] {f : X → Y} [inst : IsSmooth f] : HasAdjDiff f := sorry


syntax " IsSmooth " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec $assumptions1*
    IsSmooth $assumptions2* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsSmooth
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec $assumptions1*
    funProp $prop $space $assumptions2* := $prf)


syntax " IsLin " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    IsLin $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``IsLin
  let space : Ident := mkIdent ``Vec
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


syntax " HasAdjoint " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjoint $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjoint
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)


syntax " HasAdjDiff " bracketedBinder* (":=" term)? : argProp

macro_rules
| `(function_property $id:ident $parms:bracketedBinder* $[: $retType:term]? 
    argument $argSpec:argSpec  $assumptions1*
    HasAdjDiff $extraAssumptions* $[:= $proof]?) => do
  let prop : Ident := mkIdent ``HasAdjDiff
  let space : Ident := mkIdent ``SemiHilbert
  let prf := proof.getD (← `(term| by first | (unfold $id; infer_instance) | infer_instance))
  `(function_property $id $parms* $[: $retType:term]? 
    argument $argSpec  $assumptions1*
    funProp $prop $space $extraAssumptions* := $prf)

#check Eq.trans
#check uncurryN

function_properties HAdd.hAdd {X : Type} (x y : X) : X
argument (x,y) [Vec X]
  IsLin    := sorry,
  IsSmooth := by apply isLin_isSmooth,
  funTrans SciLean.differential := λ dx dy => dx + dy by sorry 
  by
    simp only
      [diff_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t)),
       HAdd.hAdd.arg_a4a5.differential_simp,
       diff_prodMk]
    done,
  funTrans SciLean.tangentMap := λ dx dy => (x + y, dx + dy)  by sorry 
  by 
    simp [tangentMap_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t))]
    simp [HAdd.hAdd.arg_a4a5.tangentMap_simp]
    done
argument (x,y) [SemiHilbert X]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := λ xy' => (xy', xy')  by sorry 
  by 
    simp [adjoint_comp (λ xy : X×X => xy.fst + xy.snd) (λ t => (x t, y t))]
    simp [HAdd.hAdd.arg_a4a5.adjoint_simp]
    done,
  funTrans SciLean.adjointDifferential := λ xy' => (xy', xy')  by sorry by sorry
argument x
  IsSmooth [Vec X] := by infer_instance,
  HasAdjDiff [SemiHilbert X] := by infer_instance,
  funTrans SciLean.differential [Vec X] := λ dx => dx by
    simp [HAdd.hAdd.arg_a4a5.differential_simp']
    done
  by
    sorry,
  funTrans SciLean.tangentMap [Vec X] := λ dx => (x+y, dx) by 
    simp [HAdd.hAdd.arg_a4a5.differential_simp', tangentMap]
    done
  by
    sorry
argument y
  IsSmooth [Vec X] := by apply HAdd.hAdd.arg_a4a5.IsSmooth',
  HasAdjDiff [SemiHilbert X] := by apply HAdd.hAdd.arg_a4a5.HasAdjDiff',
  funTrans SciLean.differential [Vec X] := λ dy => dy by 
    rw [HAdd.hAdd.arg_a4a5.differential_simp']; simp
    done
  by
    sorry

#check HAdd.hAdd.arg_a5.differential_simp


example {X} [Vec X] (y : X) : IsSmooth λ x : X => x + y := by infer_instance
example {X} [Vec X] (y : X) : IsSmooth λ x : X => y + x := by infer_instance

#check HAdd.hAdd.arg_a4a5.IsSmooth

#check HAdd.hAdd.arg_a4a5.differential
#check HAdd.hAdd.arg_a4a5.differential_simp
#check HAdd.hAdd.arg_a4a5.differential_simp'
#check HAdd.hAdd.arg_a4a5.tangentMap
#check HAdd.hAdd.arg_a4a5.tangentMap_simp
#check HAdd.hAdd.arg_a4a5.tangentMap_simp'

#check HAdd.hAdd.arg_a4.IsSmooth
#check HAdd.hAdd.arg_a5.IsSmooth'
#check HAdd.hAdd.arg_a5.differential_simp


def foo {α β γ : Type} (a : α) (b : β) (c : γ) : γ := sorry

function_properties SciLean.foo {α β γ : Type} (a : α) (b : β) (c : γ)
argument (a,c) [Vec α] [Vec γ]
  IsLin := sorry,
  IsSmooth := isLin_isSmooth,
  funTrans SciLean.differential := sorry by sorry by sorry,
  funTrans SciLean.tangentMap := sorry by sorry by sorry
argument (a,c) [SemiHilbert α] [SemiHilbert γ]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := sorry  by sorry by sorry,
  funTrans SciLean.adjointDifferential := sorry  by sorry by sorry,
  funTrans SciLean.reverseDifferential := sorry  by sorry by sorry
argument (a,b,c) [SemiHilbert α] [SemiHilbert β] [SemiHilbert γ]
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  funTrans SciLean.adjoint := λ c => (0,0,c) by sorry 
  by 
    simp only 
         [adjoint_comp (λ abc : α×β×γ => foo abc.1 abc.2.1 abc.2.2) (λ t => (a t, b t, c t)),
          adjoint_prodMk,
          foo.arg_abc.adjoint_simp,
          add_assoc]
    done,
  funTrans SciLean.adjointDifferential := sorry  by sorry by sorry,
  funTrans SciLean.reverseDifferential := sorry  by sorry by sorry

#check foo.arg_ac.adjoint
#check foo.arg_ac.adjointDifferential


#eval printFunctionTheorems
