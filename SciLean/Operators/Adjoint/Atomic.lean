-- import SciLean.Categories.Lin
import SciLean.Operators.Adjoint.AtomicAdjointFun

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {U V Z : Type} [Hilbert U] [Hilbert V] [Hilbert W]

@[reducible]
instance : AtomicAdjointFun (λ x : X => (0 : Y)) where
  adj := λ y => (0 : X)
  has_adjoint := sorry
  is_adj := sorry

@[reducible]
instance : AtomicAdjointFun (Prod.fst : X×Y → X) where
   adj := λ x => (x,0)
   has_adjoint := sorry
   is_adj:= sorry

@[reducible]
instance : AtomicAdjointFun (Prod.snd : X×Y → Y) where
  adj := λ y => (0,y)
  has_adjoint := sorry
  is_adj:= sorry

@[reducible]
instance : AtomicAdjointFun (λ x : X => - x) where
  adj := λ x => -x
  has_adjoint := sorry
  is_adj:= sorry

@[reducible]
instance (r : ℝ) : AtomicAdjointFun (λ x : X => r * x) where
  adj := λ x => r * x
  has_adjoint := sorry
  is_adj := sorry

@[reducible]
instance : AtomicAdjointFun₂ (λ (r : ℝ) (x : U) => r * x) where
  adj₁ := λ (x y : U) => ⟪x,y⟫
  adj₂ := λ r x => r * x
  has_adjoint₁ := sorry
  has_adjoint₂ := by infer_instance
  is_adj₁ := sorry
  is_adj₂ := by simp

@[reducible]
instance : AtomicAdjointFun (λ ((x,y) : X×X) => x + y) where
  adj := λ x => (x,x)
  has_adjoint := sorry
  is_adj := sorry

@[reducible]
instance : AtomicAdjointFun (λ ((x,y) : X×X) => x - y) where
  adj := λ x => (x,-x)
  has_adjoint := sorry
  is_adj := sorry

@[reducible]
instance : AtomicAdjointFun₂ (λ (x y : U) => ⟪x, y⟫) where
  adj₁ := λ y r => r * y
  adj₂ := λ x r => r * x
  has_adjoint₁ := sorry
  has_adjoint₂ := sorry
  is_adj₁ := sorry
  is_adj₂ := sorry

@[reducible]
instance {ι} [Enumtype ι] : AtomicAdjointFun (sum : (ι → X) → X) where
  adj := λ x i => x
  has_adjoint := sorry
  is_adj:= sorry
