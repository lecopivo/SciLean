import SciLean

import SciLean.Examples.GMM.Simps
import SciLean.Examples.GMM.SumSimproc

namespace SciLean.Examples.GMM

open Scalar

variable {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

noncomputable
def likelihood (x : R^[D]^[N]) (w : R^[K]) (μ : R^[D]^[K]) (S : R^[D,D]^[K]) : R :=
  ∏ i, ∑ k, w[k] * gaussianS (μ[k]) (S[k]) (x[i])

-- parametrization of gaussian variance σ
namespace Param
  def Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : R^[D,D] := q.exp.diag + l.lowerTriangular D 1

  def_rev_deriv Q in q l by
    unfold Q
    data_synth => lsimp

  def_rev_deriv' Q in q l by
    unfold Q
    data_synth => lsimp

  variable (q : R^[D]) (l : R^[((D-1)*D)/2])

  -- properties of parametrization
  theorem det_Q : (Q q l).det = exp q.sum := sorry_proof
  theorem det_QTQ : ((Q q l)ᵀ * (Q q l)).det = exp (2 * q.sum) := by
    simp[DataArrayN.det_mul,det_Q,exp_pull]; ring_nf
  theorem Q_invertible : (Q q l).Invertible := sorry_proof
  theorem QTQ_invertible : ((Q q l)ᵀ * (Q q l)).Invertible := sorry_proof
  theorem trace_QTQ : ((Q q l)ᵀ * Q q l).trace = ‖q.exp‖₂² + ‖l‖₂² := sorry_proof
  theorem trace_invQTQ : (((Q q l)ᵀ * Q q l)⁻¹).trace = - ‖q.exp‖₂² - ‖l‖₂² := sorry_proof

  attribute [simp, simp_core] det_Q det_QTQ Q_invertible trace_QTQ trace_invQTQ
end Param

open Param in
def likelihood' (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  likelihood x (α.softmax) μ (⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹)
  rewrite_by
    unfold likelihood
    simp (disch:=aesop) [gaussianS_ATA]



def _root_.SciLean.Scalar.tgamma (x : R) : R := x
def _root_.SciLean.Scalar.lgamma (x : R) : R := log x
def _root_.SciLean.Scalar.tgammaMulti (d : ℕ) (x : R) : R := x
def _root_.SciLean.Scalar.lgammaMulti (d : ℕ) (x : R) : R := log x

@[simp, simp_core]
theorem log_tgamma (x : R) : log (tgamma x) = lgamma x := sorry
@[simp, simp_core]
theorem log_tgammaMulti (d : ℕ) (x : R) : log (tgammaMulti d x) = lgammaMulti d x := sorry

-- source: https://en.wikipedia.org/wiki/Wishart_distribution#Probability_density_function
noncomputable
def wishartDensity {p : Nat} (V : R^[p,p]) (n : R) (X : R^[p,p]) : R :=
  let C := 1 / (2 ^ (n*p/2) * V.det ^ (n/2) * tgammaMulti p (n/2))
  C * X.det^((n-p-1)/2) * exp (-1/2*(V⁻¹*X).trace)


noncomputable
def prior (γ m : R) (S : R^[D,D]^[K]) :=
  (let n := (m + D + 1)
   ∏ k, wishartDensity (γ^(-2:R) • 𝐈) n (S[k]))


open Param Scalar in
def loss (γ m : R) (x : R^[D]^[N]) (α : R^[K]) (μ : R^[D]^[K]) (q : R^[D]^[K]) (l : R^[((D-1)*D)/2]^[K]) : R :=
  (let S := ⊞ k => ((Q q[k] l[k])ᵀ * Q q[k] l[k])⁻¹
   (- log (likelihood x (α.softmax) μ S * prior γ m S)))
  rewrite_by
    unfold likelihood
    simp (disch:=aesop) [gaussianS_ATA]

    simp (disch:=aesop) [simp_core, likelihood, prior, DataArrayN.softmax_def, wishartDensity]
    simp only [simp_core, sum_simproc, refinedRewritePost, sum_push, gaussian,
               log_push,exp_pull]
    --ring_nf




set_option pp.deepTerms true
set_option trace.Meta.Tactic.data_synth true in

def_rev_deriv loss in α μ q l by
  unfold loss
  data_synth => lsimp -zeta +singlePass only [simp_core]
