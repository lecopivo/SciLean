import SciLean.Data.ArraySet

import SciLean.Core.Meta.FunctionProperty.NormalTheorem
import SciLean.Core.Meta.FunctionProperty.CompTheorem
import SciLean.Core.Meta.FunctionProperty.EnvExtension

import SciLean.Core.Meta.RewriteBy

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
private def constArgSuffix (constName : Name) (argIds : ArraySet Nat) : MetaM String := do

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
    let val ← Term.elabTermAndSynthesize (← `(by sorry_proof)) b  
    mkLambdaFVars ys val

  let info : TheoremVal :=
  {
    name := compTheoremName
    type := compTheorem
    value := proof
    levelParams := []
  }

  addDecl (.thmDecl info)
  addInstance info.name .global 1000

  addFunctionProperty constName propName mainArgIds theoremName compTheoremName none

inductive FunTransDefStx 
  | valProof (valStx : Term) (proof : TSyntax ``Lean.Parser.Tactic.tacticSeq)
  | conv     (conv : TSyntax ``Parser.Tactic.Conv.convSeq)

def addFunTransDecl (transName : Name) (useDef : Bool) (e : Expr) (xs : Array Expr) (contextVars : Array Expr) 
  (funTransDefStx : FunTransDefStx) : TermElabM Unit := do

  let f    := e.getAppFn
  let args := e.getAppArgs

  let mainArgIds ← xs.mapM (λ x => 
    args.findIdx? (λ arg => arg == x)
    |>.getDM (do throwError s!"Error in `addFunPropDecls`, argument `{← ppExpr x}` has to accur in `{← ppExpr e}!"))

  let mainArgIds := mainArgIds.toArraySet

  let .some (constName, _) := f.const?
    | throwError s!"Error in `addFunPropDecls`, the expression `{← ppExpr e}` has to be an application of a constant!"

  -- make definition
  let defTargetVal  ← mkNormalTheoremLhs transName e xs
  let defType ← inferType defTargetVal
  let (defVal, defProof)  ← 
    match funTransDefStx with
    | .valProof valStx proofStx => do
      let val ← Term.elabTermAndSynthesize valStx defType
      let prf ← Term.elabTermAndSynthesize (← `(by $proofStx)) (← mkEq defTargetVal val)
      pure (val, prf)
    | .conv rw => rewriteBy defTargetVal rw

  let defName := constName
    |>.append "arg_"
    |>.appendAfter (← constArgSuffix constName mainArgIds)
    |>.append transName.getString

  -- some function transformations remove `xs` so we need to remove them from the `contextVars`
  let contextVars' := maybeFilterContextVars transName xs contextVars
  let defValLambda ← mkLambdaFVars contextVars' defVal

  let info : DefinitionVal := 
  {
    name  := defName
    type  := ← instantiateMVars (← inferType defValLambda)
    value := ← instantiateMVars defValLambda 
    hints := .regular 0
    safety := .safe
    levelParams := []
  }

  addAndCompile (.defnDecl info)

  -- If we want to use just defined value in the simp theorem
  let defVal ← 
    if useDef = true then do
      mkAppOptM defName (contextVars'.map some)
    else
      pure defVal

  let normalTheoremType  ← mkForallFVars contextVars' (← mkEq defTargetVal defVal)
  let normalTheoremProof ← mkLambdaFVars contextVars' defProof

  IO.println s!"Normal theorem for {transName}:\n{← ppExpr normalTheoremType}"

  let theoremName := defName.appendAfter "_simp"

  let info : TheoremVal :=
  {
    name  := theoremName
    type  := ← instantiateMVars normalTheoremType
    value := ← instantiateMVars normalTheoremProof
    levelParams := []
  }

  addDecl (.thmDecl info)

  let compTheorem ← mkCompTheorem transName e xs contextVars defVal

  IO.println s!"Composition theorem for {transName}:\n{← ppExpr compTheorem}"

  let prf ← forallTelescope compTheorem λ contextVars statement => do
    -- TODO: Fill the proof here!!! 
    -- I think I can manually apply composition rule and then it should be 
    -- automatically discargable by using the normal theorem and product rule
    let prf ← Term.elabTermAndSynthesize (← `(by sorry_proof)) statement
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

  addFunctionProperty constName transName mainArgIds theoremName compTheoremName defName

