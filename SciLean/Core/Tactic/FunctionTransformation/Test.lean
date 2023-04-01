import SciLean.Core.Defs
import SciLean.Core.Tactic.FunctionTransformation.AttribInit
import SciLean.Core.Tactic.FunctionTransformation.Core

namespace SciLean


#check differential

@[fun_trans_def]
def diff {X Y} [Vec X] [Vec Y] (f : X → Y) : X → X → Y := sorry

@[fun_trans_def]
def inv {X Y} [Nonempty X] (f : X → Y) : Y → X := sorry


@[fun_trans_rule]
theorem diff_id (X) [Vec X]
  : diff (λ x : X => x)
    =
    λ x dx => dx := sorry

@[fun_trans_rule]
theorem diff_const {X} (Y : Type) [Vec X] [Vec Y] (x : X)
  : diff (λ y : Y => x)
    =
    λ y dy => 0 := sorry

@[fun_trans_rule]
theorem diff_comp {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : Y → Z) (g : X → Y)
  : diff (λ x : X => f (g x))
    =
    λ x dx => diff f (g x) (diff g x dx) := sorry

@[fun_trans_rule]
theorem diff_swap {α X Y : Type} [Vec X] [Vec Y]
  (f : α → X → Y) 
  : diff (λ (x : X) (a : α) => f a x)
    =
    λ x dx a => diff (f a) x dx := sorry

@[fun_trans_rule]
theorem diff_forallMap {α X Y : Type} [Vec X] [Vec Y]
  (f : α → X → Y)
  : diff (λ (g : α → X) (a : α) => f a (g a))
    =
    λ g dg a => diff (f a) (g a) (dg a) := sorry

@[fun_trans_rule]
theorem diff_eval {α} (X) [Vec X] (a : α)
  : diff (λ (f : α → X) => f a)
    =
    λ f df => df a := sorry

@[fun_trans_rule]
theorem diff_prodMap {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y) (g : X → Z)
  : diff (λ x => (f x, g x))
    =
    λ x dx => (diff f x dx, diff g x dx) := sorry


@[fun_trans_rule]
theorem diff_letBinop {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : X → Y → Z) (g : X → Y)
  : diff (λ (x : X) => let y := g x; f x y)
    =
    λ x dx =>
      let y  := g x
      let dy := diff g x dx 
      diff (λ xy => f xy.1 xy.2) (x,y) (dx,dy) := sorry

@[fun_trans_rule]
theorem diff_letComp {X Y Z} [Vec X] [Vec Y] [Vec Z]
  (f : Y → Z) (g : X → Y)
  : diff (λ (x : X) => let y := g x; f y)
    =
    λ x dx =>
      let y  := g x
      let dy := diff g x dx 
      diff f y dy := sorry

@[fun_trans]
theorem diff_fst (X Y) [Vec X] [Vec Y]
  : diff (λ (xy : X×Y) => xy.1)
    =
    λ xy dxy => dxy.1 := sorry

#eval show IO Unit from do

  let rules ← funTransRulesMapRef.get 
  IO.println s!"{String.join (rules.toList.map (λ r => toString r ++ "\n"))}"

@[fun_trans_rule]
theorem inv_id (X) [Nonempty X]
  : inv (λ x : X => x)
    =
    λ x => x := sorry


#check (2 + 4) rewrite_by simp; trace_state

variable {α β γ : Type} {X Y Y₁ Y₂ Z : Type} [Vec X] [Vec Y] [Vec Z] [Vec Y₁] [Vec Y₂]

set_option pp.all true in
set_option trace.Meta.Tactic.fun_trans true 
set_option trace.Meta.Tactic.fun_trans.rewrite true 
set_option trace.Meta.Tactic.fun_trans.missing_rule true
set_option trace.Meta.Tactic.fun_trans.normalize_let true 

example
  : diff (λ x : X => x) 
    = 
    λ x dx => dx 
  := by fun_trans


example (x : X)
  : diff (λ y : Y => x) y
    = 
    λ dy => 0
  := by fun_trans

example (a : α) (f : α → X)
  : diff (λ f' : α → X => f' a) f
    = 
    λ df => df a
  := by fun_trans


example (f : Y → Z) (g : X → Y)
  : diff (λ x : X => f (g x))
    = 
    λ x dx => diff f (g x) (diff g x dx)
  := by fun_trans


example (f : X → Y → Z) (g : X → Y)
  : diff (λ x : X => f x (g x))
    = 
    λ x dx => diff (uncurryN 2 f) (x, g x) (dx, diff g x dx)
  := by fun_trans


example (f : Y₁ → Y₂ → Z) (g₁ : X → Y₁) (g₂ : X → Y₂)
  : diff (λ x : X => f (g₁ x) (g₂ x))
    = 
    λ x dx => diff (uncurryN 2 f) (g₁ x, g₂ x) (diff g₁ x dx, diff g₂ x dx)
  := by fun_trans


example {ι : Type} [Enumtype ι] (f g : ι → X)
  : f + g = λ i => f i + g i := by rfl


example {ι : Type} [Enumtype ι] 
  : diff (λ (g : ι → X) i => g i + g i)
    =
    λ g dg i => 0
  := by fun_trans



example {ι : Type} [Enumtype ι] (p q : ℝ → ℝ) (x : ℝ)
  : diff (λ (f : ℝ → ℝ) x => f x + ⅆ f x)
    =
    λ f df => 0
  := by fun_trans


example 
  (p q f : ℝ → ℝ)
  : ((fun x => p x * f x) + fun x => q x * differentialScalar f x)
    =
    fun x => p x * f x + q x * differentialScalar f x
  := by rfl

example {ι : Type} [Enumtype ι] (p q : ℝ → ℝ) (x : ℝ) (c : ℝ)
  : diff (λ (f : ℝ → ℝ) => x * f x)
    =
    λ f df => 0
  := by fun_trans
