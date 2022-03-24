import SciLean.Mathlib.Data.PowType
import SciLean.Operators


namespace SciLean.PowType

variable (X : Type) (n m : Nat) [PowType X]

instance [AddSemigroup X]  : AddSemigroup (X^n)  := AddSemigroup.mk sorry
instance [AddMonoid X]     : AddMonoid (X^n)     := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance [AddCommMonoid X] : AddCommMonoid (X^n) := AddCommMonoid.mk sorry
instance [SubNegMonoid X]  : SubNegMonoid (X^n)  := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance [AddGroup X]      : AddGroup (X^n)      := AddGroup.mk sorry
instance [AddCommGroup X]  : AddCommGroup (X^n)  := AddCommGroup.mk sorry

instance [MulAction ℝ X] : MulAction ℝ (X^n) := MulAction.mk sorry sorry
instance [AddMonoid X] [DistribMulAction ℝ X] : DistribMulAction ℝ (X^n) := DistribMulAction.mk sorry sorry
instance [AddCommMonoid X] [DistribMulAction ℝ X] : Module ℝ (X^n) := Module.mk sorry sorry

instance [AddCommGroup X] [DistribMulAction ℝ X] : Vec (X^n) := Vec.mk

instance [SemiInner X] : SemiInner (X^n) :=
{
  Domain := 𝓓 X
  domain := default
  semiInner := λ x y Ω => ∑ i, ⟪x[i], y[i]⟫[Ω]
  testFunction := λ _ _ => True
}

instance [SemiHilbert X] : SemiHilbert (X^n) :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
  semi_inner_gtr := sorry
}

instance [Hilbert X] : Hilbert (X^n) :=
{
  uniqueDomain := sorry
}


variable [Vec X]

instance : IsSmooth   (λ (c : X^n) (i : Fin n)  => c[i]) := sorry
instance : IsLin      (λ (c : X^n) (i : Fin n)  => c[i]) := sorry
-- instance (i : Fin n) : IsSmooth   (λ c : X^n => c[i]) := by infer_instance
-- instance (i : Fin n) : IsLin      (λ c : X^n => c[i]) := by infer_instance

@[simp]
theorem diff_of_powtype_getOp
  : δ (λ (x : X^n) (i : Fin n) => x[i]) = λ x dx i => dx[i] := sorry

variable [Hilbert X]
instance : HasAdjoint (λ (c : X^n) (i : Fin n) => c[i]) := sorry
-- instance (i : Fin n) : HasAdjoint (λ c : X^n => c[i]) := by infer_instance

@[simp]                         
theorem adjoint_of_powtype_get
  : (λ (c : X^n) i => c[i])† = PowType.intro := sorry
