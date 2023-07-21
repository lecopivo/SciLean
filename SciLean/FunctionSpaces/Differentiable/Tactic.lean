import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.FunctionSpaces.Differentiable.Basic
import SciLean.Profile

set_option profiler true

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean Lean Meta Qq


def Differentiable.discharger (e : Expr) : SimpM (Option Expr) := do
  return none


open Lean Elab Term FProp
def Differentiable.fpropExt : FPropExt where
  fpropName := ``Differentiable
  getFPropFun? e := 
    if e.isAppOf ``Differentiable then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``Differentiable then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  identityRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Differentiable.id_rule 
      origin := .decl ``Differentiable.id_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Differentiable.const_rule 
      origin := .decl ``Differentiable.const_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule    e := 
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Differentiable.let_rule 
      origin := .decl ``Differentiable.let_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLambdaRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Differentiable.pi_rule 
      origin := .decl ``Differentiable.pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger e := return none


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``Differentiable, Differentiable.fpropExt))


@[fprop_rule]
theorem HAdd.hAdd.arg_a4a5.Differentiable_comp'
  (R : Type _) [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  (f g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g)
  : Differentiable R fun x => f x + g x
  := fun x => HAdd.hAdd.arg_a4a5.DifferentiableAt_comp x f g (hf x) (hg x)



example : Differentiable ℝ (fun x : ℝ => x) := by fprop

example (y : ℝ) : Differentiable ℝ (fun _ : ℝ => y + y) := by fprop

example : Differentiable ℝ (fun x : ℝ => x + x) := by fprop

example : Differentiable ℝ (fun x : ℝ => x + x + x + x) := by fprop

theorem a : Differentiable ℝ (fun x : ℝ => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + (x + x) + x + (x + x + x + x + x + x) + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x) := by fprop

example (x : ℝ) : Differentiable ℝ (HAdd.hAdd x) := by fprop

example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ f := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x + x) := by fprop
example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f x + f x) := by fprop

-- set_option trace.Meta.Tactic.fprop.step true

example (f : ℝ → ℝ) (hf : Differentiable ℝ f) : Differentiable ℝ (fun x => f (f x)) := by (try fprop); sorry


-- set_option trace.Meta.Tactic.fprop.unify true
-- set_option trace.Meta.Tactic.fprop.apply true
-- set_option trace.Meta.Tactic.fprop.discharge true


example (op : ℝ → ℝ → ℝ) (hop : Differentiable ℝ (fun (x,y) => op x y)) 
  (f : ℝ → ℝ) (hf : Differentiable ℝ f)
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  : Differentiable ℝ (fun x => op (f x) (g x)) := by (try fprop); sorry


example 
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (fun (x,y) => f x y))
  : Differentiable ℝ (fun x => f x (g x)) := by fprop

example 
  (g : ℝ → ℝ) (hg : Differentiable ℝ g)
  (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (fun (x,y) => f x y))
  : Differentiable ℝ (fun x => let y := g x; f x y) := by fprop

example (f : ι → ℝ → ℝ) (i : ι) (hf : ∀ i, Differentiable ℝ (f i))
  : Differentiable ℝ (fun x => f i x) := by fprop

example (f : ι → ℝ → ℝ) (i : ι) (hf : ∀ i, Differentiable ℝ (f i))
  : Differentiable ℝ (f i) := by fprop


example [Fintype ι] (f : ℝ → ι → ℝ) (hf : ∀ i, Differentiable ℝ (fun x => f x i))
  : Differentiable ℝ (fun x i => f x i) := by fprop


theorem b [Fintype ι] (f : ℝ → ι → ℝ) (hf : ∀ i, Differentiable ℝ (fun x => f x i))
  : ∀ i, Differentiable ℝ (fun x => f x i) := by fprop


@[fprop_rule]
theorem Prod.fst.arg_self.Differentiable_comp'
  (R : Type _) [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  (f : X → Y×Z) (hf : Differentiable R f)
  : Differentiable R (fun x => (f x).1)
  := Differentiable.fst hf


@[fprop_rule]
theorem Prod.snd.arg_self.Differentiable_comp'
  (R : Type _) [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  (f : X → Y×Z) (hf : Differentiable R f)
  : Differentiable R (fun x => (f x).2)
  := Differentiable.snd hf


example : Differentiable ℝ (fun x : ℝ => let y := x + x; y) := by fprop


theorem hoho : Differentiable ℝ (fun x : ℝ => let y := x + x + x + x + x + (x + x + x + x + x + x + x + x + x + x + (x + x + x) + x) + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + (x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x + x + x + x); y + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x+ x + x + x + x + x + x + x) := by fprop




