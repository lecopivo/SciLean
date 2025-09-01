-- import SciLean.Data.VectorType.Operations.Exp
-- import SciLean.Data.VectorType.Operations.Sum
-- import SciLean.Data.VectorType.Operations.Mul
-- import SciLean.Data.VectorType.Operations.Axpy
-- import SciLean.Analysis.SpecialFunctions.Log

-- namespace SciLean

-- open VectorType

-- section Simps

-- variable
--   {X : Type*} {I : Type u} {R :  Type*}
--   {_ : RealScalar R} {nI} {_ : IndexType I nI} [VectorType.Base X I R] [Dense X]

-- theorem VectorType.softmax_spec (x : X) :
--   VectorType.softmax x
--   =
--   let x' := exp x
--   let w := sum x'
--   w⁻¹ • x' := sorry_proof

-- end Simps

-- def_fun_prop softmax in x with_transitive [InjectiveGetElem X n] : Differentiable R by
--   -- simp only [softmax_spec]
--   -- have h : ∀ (w : X), sum (exp w) ≠ 0 := sorry_proof
--   -- fun_prop (disch:=sorry_proof)
--   sorry_proof

-- -- fderiv
-- abbrev_fun_trans softmax in x [InjectiveGetElem X n] : fderiv R by
--   equals (fun x => fun dx =>L[R]
--            let x' := softmax x
--            let s := - ⟪dx, x'⟫[R]
--            axpy s x' (mul x' dx)) =>
--     sorry_proof

-- abbrev_data_synth softmax in x [InjectiveGetElem X n] (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
--   apply hasFDerivAt_from_fderiv
--   case deriv => conv => rhs; autodiff
--   case diff => dsimp[autoParam]; fun_prop

-- -- forward AD
-- abbrev_fun_trans softmax in x [InjectiveGetElem X n] : fwdFDeriv R by
--   unfold fwdFDeriv
--   fun_trans; to_ssa

-- -- reverse AD
-- abbrev_fun_trans softmax in x [InjectiveGetElem X n] : revFDeriv R by
--   unfold revFDeriv
--   fun_trans; to_ssa

-- abbrev_data_synth softmax in x [InjectiveGetElem X n] : HasRevFDeriv R by
--   apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
--   case deriv => intros; data_synth
--   case adjoint => intros; dsimp; data_synth
--   case simp => conv => rhs; simp [vector_optimize]; to_ssa; to_ssa; lsimp

-- abbrev_data_synth softmax in x [InjectiveGetElem X n] : HasRevFDerivUpdate R by
--   apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
--   case deriv => intros; data_synth
--   case adjoint => intros; dsimp; data_synth
--   case simp => conv => rhs; simp [vector_optimize]; to_ssa; to_ssa; lsimp
