import SciLean.Core

namespace SciLean

-- TODO: MOVE THIS FILE SOMEWHERE ELSE

-- todo: currently these rotations can mirror flip!!! add a requirement that they preserve
-- orientation
structure Rotation (R : Type _) [RealScalar R] (X : Type _) [SemiHilbert R X]
  extends X ≃ X where
  is_linear_map : IsLinearMap R toFun
  is_isometry : ∀ x, ‖x‖₂[R] = ‖toFun x‖₂[R]

variable
  {R} [RealScalar R]
  {X} [SemiHilbert R X]

instance : EquivLike (Rotation R X) X X where
  coe := fun r => r.toFun
  inv := fun r => r.invFun
  left_inv := fun r => r.left_inv
  right_inv := fun r => r.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    cases e₁; cases e₂
    simp_all only [Equiv.toFun_as_coe, DFunLike.coe_fn_eq, Equiv.invFun_as_coe]
