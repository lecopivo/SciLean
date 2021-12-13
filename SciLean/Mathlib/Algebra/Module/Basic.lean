import Mathlib.Algebra.Ring.Basic

class MulAction (α : Type u) (β : Type v) [Monoid α] extends HMul α β β :=
(one_smul : ∀ b : β, (1 : α) * b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) * b = x * y * b)

class DistribMulAction (M : Type u) (A : Type v) [Monoid M] [AddMonoid A]
  extends MulAction M A :=
(smul_add : ∀(r : M) (x y : A), r * (x + y) = r * x + r * y)
(smul_zero : ∀(r : M), r * (0 : A) = 0)

class Module (R : Type u) (M : Type v) [Semiring R]
  [AddCommMonoid M] extends DistribMulAction R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) * x = r * x + s * x)
(zero_smul : ∀x : M, (0 : R) * x = 0)
