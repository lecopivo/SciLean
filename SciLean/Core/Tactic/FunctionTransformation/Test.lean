import SciLean.Core.Defs
import SciLean.Core.Tactic.FunctionTransformation.AttribInit

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
theorem diff_letE {X Y Z} [Vec X] [Vec Y] [Vec Z]
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


@[fun_trans_rule]
theorem inv_id (X) [Nonempty X]
  : inv (λ x : X => x)
    =
    λ x => x := sorry
