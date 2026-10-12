module

public import SciLean.Analysis.Calculus.FwdFDeriv
public import SciLean.Analysis.Calculus.RevFDeriv
public import SciLean.Meta.GenerateFunProp

@[expose] public section

-- import SciLean.Meta.GenerateFunTrans

namespace SciLean

set_option deprecated.oldSectionVars true

open ComplexConjugate

variable
  {R K : Type*} [RealScalar R] [Scalar R K] [ScalarSMul R K] [ScalarInner R K]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X] [NormedSpace K X]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace R U] [AdjointSpace K U] [CompleteSpace U]


theorem Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule :
    IsBoundedBilinearMap R (fun (x : U×U) => ⟪x.1,x.2⟫[K]) := by
  obtain ⟨C, hC, hCle⟩ := AdjointSpace.exists_norm_inner_le (𝕜:=K) (E:=U)
  have h0 : ∀ y : U, IsContinuousLinearMap R (fun x : U => ⟪x, y⟫[K]) :=
    fun y => Inner.inner.arg_a0.IsContinuousLinearMap_rule (fun x => x) (by fun_prop) y
  have h1 : ∀ x : U, IsContinuousLinearMap R (fun y : U => ⟪x, y⟫[K]) :=
    fun x => Inner.inner.arg_a1.IsContinuousLinearMap_rule_real (fun y => y) (by fun_prop) x
  constructor
  · intro x₁ x₂ y; exact AdjointSpace.inner_add_left _ _ _
  · intro c x y; exact (h0 y).linear.map_smul c x
  · intro x y₁ y₂; exact AdjointSpace.inner_add_right _ _ _
  · intro c x y; exact (h1 x).linear.map_smul c y
  · exact ⟨C, hC, fun x y => by rw [mul_assoc]; exact hCle x y⟩


def_fun_prop with_transitive : Differentiable R (fun (x : U×U) => ⟪x.1,x.2⟫[K]) by
  fun_prop (disch:=apply Inner.inner.arg_a0a1.IsBoundedBilinearMap_rule)

def_fun_prop with_transitive _real : Differentiable R (fun (x : U×U) => ⟪x.1,x.2⟫[R]) by
  fun_prop

-- abbrev_fun_trans (x : U×U) : fderiv R (fun x : U×U => ⟪x.1, x.2⟫[R]) x by
--   equals (fun dx =>L[R] ⟪x.1,dx.2⟫[R] + ⟪dx.1,x.2⟫[R]) => sorry_proof

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.fderiv_rule :
  fderiv R (fun x : U×U => ⟪x.1, x.2⟫[K])
  =
  fun x => fun dx =>L[R]
    let' (x,y) := x
    let' (dx,dy) := dx
    let s₁ := ⟪x,dy⟫[K]
    let s₂ := ⟪dx,y⟫[K]
    s₁ + s₂ := by
  funext x
  -- the inner product is a bounded bilinear map, hence the remainder `⟪dx.1,dx.2⟫` is `o(‖dx‖)`
  obtain ⟨C, hC, hCle⟩ := AdjointSpace.exists_norm_inner_le (𝕜:=K) (E:=U)
  apply HasFDerivAt.fderiv
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrem : (fun h : U×U => ⟪(x+h).1, (x+h).2⟫[K] - ⟪x.1,x.2⟫[K]
        - ((fun dx =>L[R]
              let' (x,y) := x
              let' (dx,dy) := dx
              let s₁ := ⟪x,dy⟫[K]
              let s₂ := ⟪dx,y⟫[K]
              s₁ + s₂) h))
      = fun h : U×U => ⟪h.1,h.2⟫[K] := by
    funext h
    simp only [ContinuousLinearMap.mk'_eval, Prod.fst_add, Prod.snd_add,
      AdjointSpace.inner_add_left, AdjointSpace.inner_add_right]
    abel
  rw [hrem, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [Metric.ball_mem_nhds (0 : U×U) (by positivity : 0 < c/C)] with h hh
  have hh' : ‖h‖ < c/C := by simpa [dist_eq_norm] using hh
  have h1 : ‖h.1‖ ≤ ‖h‖ := le_max_left _ _
  have h2 : ‖h.2‖ ≤ ‖h‖ := le_max_right _ _
  calc ‖⟪h.1,h.2⟫[K]‖ ≤ C * (‖h.1‖ * ‖h.2‖) := hCle _ _
    _ ≤ C * (‖h‖ * ‖h‖) := by
        have := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left this hC.le
    _ ≤ c * ‖h‖ := by
        have : C * ‖h‖ ≤ c := by
          rw [← le_div_iff₀' hC]
          exact hh'.le
        nlinarith [norm_nonneg h]

@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.fwdFDeriv_rule :
  fwdFDeriv R (fun x : U×U => ⟪x.1, x.2⟫[K])
  =
  fun x dx =>
    let' (x,y) := x
    let' (dx,dy) := dx
    let s₀ := ⟪x,y⟫[K]
    let s₁ := ⟪x,dy⟫[K]
    let s₂ := ⟪dx,y⟫[K]
    (s₀, s₁ + s₂) := by unfold fwdFDeriv; fun_trans


@[fun_trans]
theorem _root_.Inner.inner.arg_a0a1.revFDeriv_rule :
  revFDeriv R (fun x : U×U => ⟪x.1, x.2⟫[K])
  =
  fun x =>
    let' (x,y) := x
    let s := ⟪x,y⟫[K]
    (s, fun dr =>
      let dy := conj dr • y
      let dx := dr • x
      (dy, dx)) := by unfold revFDeriv; fun_trans
