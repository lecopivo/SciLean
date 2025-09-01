import SciLean

/-! Simp theorems to make GMM example work

 TODO: redistribute them to appropriate locations

-/

open SciLean Scalar SciLean.Meta

variable {R} [RealScalar R] [PlainDataType R]
variable {I : Type} [IndexType I]
variable {J : Type} [IndexType J]

set_default_scalar R

attribute [-simp_core] SciLean.ArrayType.sum_ofFn
attribute [rsimp] SciLean.ArrayType.sum_ofFn


@[simp, simp_core]
theorem DataArrayN.inv_smul (c : R) (A : R^[n,n]) : (c•A)⁻¹ = c⁻¹•A⁻¹ := sorry_proof

@[simp, simp_core]
theorem DataArrayN.det_smul (c : R) (A : R^[n,n]) : (c•A).det = c^n*A.det := sorry_proof

@[simp, simp_core]
theorem DataArrayN.trace_smul (c : R) (A : R^[n,n]) : (c•A).trace = c*A.trace := sorry_proof


@[rsimp]
theorem IndexType.sum_const {X} [AddCommGroup X] (x : X) :
  (∑ (i : I), x) = Size.size I • x := by sorry_proof

@[simp_core]
theorem neg_add_rev' {G : Type*} [SubtractionCommMonoid G] (a b : G) : -(a + b) = -a + -b := by
  simp[add_comm]


@[rsimp]
theorem sum_normalize (x : R^[I]) : ∑ i, x[i] = x.sum := rfl

-- TODO: this theorem replaces (∑ i, ‖x[i]‖₂²) with (∑ i, ‖x[i]‖₂²) instead of ‖x‖₂²
--       there must be some issue with transparency
omit [PlainDataType R] in
@[rsimp]
theorem norm_normalize {X} [PlainDataType X] [NormedAddCommGroup X] [AdjointSpace R X] (x : X^[I]) :
  (∑ i, ‖x[i]‖₂²) = ‖x‖₂² := rfl

-- theorem sum_over_prod {R} [AddCommMonoid R] {I J : Type*} [IndexType I] [IndexType J]
--     {f : I → J → R} : ∑ i j, f i j = ∑ (i : I×J), f i.1 i.2  := sorry

@[rsimp]
theorem isum_sum (x : R^[I]^[J]) : ∑ i, x[i].sum = x.uncurry.sum := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry]
  rw[sum_sum_eq_sum_prod]

@[rsimp]
theorem isum_norm_exp (x : R^[I]^[J]) :
    ∑ j, ‖x[j].exp‖₂² = ‖x.uncurry.exp‖₂² := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry,
       DataArrayN.norm2_def,DataArrayN.exp]
  rw[sum_sum_eq_sum_prod]

@[rsimp]
theorem isum_norm (x : R^[I]^[J]) :
    (∑ j, ‖x[j]‖₂²) = ‖x.uncurry‖₂² := by
  simp[DataArrayN.uncurry_def,DataArrayN.sum,Function.HasUncurry.uncurry,
       DataArrayN.norm2_def]
  rw[sum_sum_eq_sum_prod]
