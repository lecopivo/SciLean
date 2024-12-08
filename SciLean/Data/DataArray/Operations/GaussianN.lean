import SciLean.Data.DataArray.Operations.Vecmul
import SciLean.Data.DataArray.Operations.Simps
import SciLean.Data.DataArray.Operations.Transpose
import SciLean.Analysis.SpecialFunctions.Exp
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Analysis.SpecialFunctions.Gaussian
import SciLean.Meta.Notation.Let'

namespace SciLean

variable {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

open Scalar RealScalar

/-- Symbolic n-dimansional gaussian.

The reason why it is symbolic is that you do not want to compute deteminant and inverse of `σ`. -/
noncomputable
def gaussianS {n : ℕ} (μ : R^[n]) (S : R^[n,n]) (x : R^[n]) : R :=
  let x' := x-μ
  (2*π)^(-(n:R)/2) * S.det^(-(1:R)/2) * exp (- ⟪x', (S⁻¹)*x'⟫/2)


def_fun_prop gaussianS in μ x : Differentiable R


abbrev_fun_trans gaussianS in μ x : fderiv R by
  equals (fun μx => fun dμx : R^[n]×R^[n] =>L[R]
          let' (μ,x) := μx
          let' (dμ,dx) := dμx
          let x' := x-μ
          let dx' := dx-dμ
          let G := gaussianS μ S x
          let ds := ⟪dx',S⁻¹*x'⟫[R] + ⟪x',S⁻¹*dx'⟫[R]
          (-2⁻¹)*ds*G) =>
   unfold gaussianS
   fun_trans
   funext x; dsimp;
   ext dx <;> (simp; ring)


abbrev_fun_trans gaussianS in μ x : fwdFDeriv R by
  equals (fun μx dμx : R^[n] × R^[n] =>
          let' (μ,x) := μx
          let' (dμ,dx) := dμx
          let x' := x-μ
          let dx' := dx-dμ
          let G := gaussianS μ S x
          let ds := ⟪dx',S⁻¹*x'⟫[R] + ⟪x',S⁻¹*dx'⟫[R]
          (G,  (-2⁻¹)*ds*G)) =>
   unfold fwdFDeriv
   fun_trans


abbrev_fun_trans gaussianS in μ x : revFDeriv R by
  equals (fun μx : R^[n] × R^[n] =>
          let' (μ,x) := μx
          let x' := x-μ
          let G := gaussianS μ S x
          (G, fun dr =>
              let dx := (-2⁻¹*dr)•(S⁻ᵀ*x' + S⁻¹*x')
              (-G•dx,G•dx))) =>

   unfold revFDeriv
   fun_trans
   funext x
   simp only [Prod.mk.injEq, true_and]
   funext dr
   simp only [Prod.mk.injEq]
   constructor <;> module


open DataArrayN


omit [PlainDataType R] in
@[simp, simp_core]
theorem RealScalar.one_pow (x : R) : (1:R)^x = 1 := sorry_proof


theorem gaussianS_ATA' {μ : R^[n]} {A : R^[n,n]} {x : R^[n]} (hA : A.Invertible) :
    gaussianS μ ((Aᵀ*A)⁻¹) x = A.det * gaussianS 0 𝐈 (A*(x-μ)) := by
  unfold gaussianS
  simp (disch:=simp[hA]) only [det_inv_eq_inv_det, det_mul, det_transpose, mul_inv_rev,
  DataArrayN.inv_inv, vecmul_assoc, transpose_transpose, inner_self, det_identity, mul_one,
  sub_zero, inv_identity,identity_vecmul, mul_eq_mul_right_iff,RealScalar.one_pow,inner_ATA_right]
  ring_nf
  have h : (A.det ^ 2)⁻¹ ^ (-(1:R) / 2) = A.det := sorry_proof
  simp[h]


theorem gaussianS_ATA (μ : R^[n]) (A : R^[n,n]) (hA : A.Invertible) (x : R^[n]) :
    gaussianS μ ((Aᵀ*A)⁻¹) x = A.det * gaussian 0 1 (A*(x-μ)) := by

  rw[gaussianS_ATA' hA]
  unfold gaussian gaussianS
  simp



@[exp_push]
theorem mul_exp_gaussianS (x : R) (μ : R^[n]) (S : R^[n,n]) (y : R^[n]) :
    Scalar.exp x * gaussianS μ S y
    =
    let y' := y-μ
    (2*π)^(-(n:R)/2) * S.det^(-(1:R)/2) * Scalar.exp (- ⟪y', (S⁻¹)*y'⟫/2 + x) := by
  unfold gaussianS
  rw [mul_comm]
  simp only [mul_assoc,exp_pull]

@[exp_push]
theorem mul_gaussianS_exp (μ : R^[n]) (S : R^[n,n]) (x : R^[n]) (y : R) :
    gaussianS μ S x * Scalar.exp y
    =
    let x' := x-μ
    (2*π)^(-(n:R)/2) * S.det^(-(1:R)/2) * Scalar.exp (- ⟪x', (S⁻¹)*x'⟫/2 + y) := by
  unfold gaussianS
  simp only [mul_assoc,exp_pull]
