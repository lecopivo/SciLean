import SciLean.Core

open SciLean

variable
  {K} [IsROrC K]
  {X Y Z W} [Vec K X] [Vec K Y] [Vec K Z] [Vec K W]


section TwoArguments
variable   (f : X → Y → Z)   (hf : CDifferentiable K fun xy : X×Y => f xy.1 xy.2)

example : ∀ x, CDifferentiable K fun y => f x y := by fun_prop
example : ∀ y, CDifferentiable K fun x => f x y := by fun_prop
example : CDifferentiable K f := by fun_prop

end TwoArguments


section ThreeArguments
variable (f : X → Y → Z → W) (hf : CDifferentiable K fun xyz : X×Y×Z => f xyz.1 xyz.2.1 xyz.2.2)

example : ∀ y z, CDifferentiable K fun x => f x y z := by fun_prop
example : ∀ x z, CDifferentiable K fun y => f x y z := by fun_prop
example : ∀ x y, CDifferentiable K fun z => f x y z := by fun_prop
example : ∀ x, CDifferentiable K fun yz : Y×Z => f x yz.1 yz.2 := by fun_prop
example : ∀ x, CDifferentiable K fun zy : Z×Y => f x zy.2 zy.1 := by fun_prop
example : ∀ y, CDifferentiable K fun xz : X×Z => f xz.1 y xz.2 := by fun_prop
example : ∀ y, CDifferentiable K fun zx : Z×X => f zx.2 y zx.1 := by fun_prop
example : ∀ z, CDifferentiable K fun xy : X×Y => f xy.1 xy.2 z := by fun_prop
example : ∀ z, CDifferentiable K fun yx : Y×X => f yx.2 yx.1 z := by fun_prop
example : CDifferentiable K f := by fun_prop
example : ∀ x, CDifferentiable K (f x) := by fun_prop
example : ∀ x y, CDifferentiable K (f x y) := by fun_prop

end ThreeArguments
