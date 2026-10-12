module

public import SciLean.Analysis.SpecialFunctions.Inner
public import SciLean.Analysis.SpecialFunctions.Pow
public import SciLean.Meta.GenerateFunProp

@[expose] public section


namespace SciLean

set_option deprecated.oldSectionVars true
set_option linter.unusedVariables false

variable
  {R : Type*} [RealScalar R]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace R X]
  {U : Type*} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]
  {V : Type*} [NormedAddCommGroup V] [AdjointSpace R V] [CompleteSpace V]

def_fun_prop with_transitive : Differentiable R (fun u : U => ‖u‖₂²[R]) by
  unfold Norm2.norm2; fun_prop [Norm2.norm2]

@[fun_trans]
theorem Norm2.norm2.arg_a0.fderiv_rule :
    fderiv R (fun x : U => ‖x‖₂²[R])
    =
    fun x => fun dx =>L[R] 2 * ⟪dx,x⟫[R] := by
  ext x dx
  fun_trans only [norm2_def,ContinuousLinearMap.mk'_eval]
  rw[← AdjointSpace.conj_symm]
  simp; ring


@[fun_trans]
theorem Norm2.norm2.arg_a0.fwdFDeriv_rule :
    fwdFDeriv R (fun x : U => ‖x‖₂²[R])
    =
    fun x dx => (‖x‖₂²[R], 2 *⟪dx,x⟫[R]) := by
  unfold fwdFDeriv
  fun_trans

@[fun_trans]
theorem Norm2.norm2.arg_a0.revFDeriv_rule :
    revFDeriv R (fun x : U => ‖x‖₂²[R])
    =
    fun x =>
      (‖x‖₂²[R], fun dy => (2 * dy) • x) := by
  unfold revFDeriv
  fun_trans [smul_smul]

theorem norm2_nonneg (R) [RealScalar R] {X} [NormedAddCommGroup X] [AdjointSpace R X] (x : X) :
    0 ≤ ‖x‖₂²[R] := by
  rw[norm2_def]
  rw[← AdjointSpace.inner_self_ofReal_re]
  have := AdjointSpace.inner_self_nonneg (𝕜:=R) (x:=x)
  sorry_proof


--  ‖·‖₂ --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def_fun_prop (x : U) (hx : x ≠ 0) : DifferentiableAt R (norm₂ R) x by
  have : ‖x‖₂²[R] ≠ 0 := sorry_proof
  unfold norm₂; fun_prop (disch:=aesop)

def_fun_prop (f : X → U) (hf : Differentiable R f) (hx' : ∀ x, f x ≠ 0) :
    Differentiable R (fun x : X => ‖f x‖₂[R]) by
  intro x;
  have : ‖f x‖₂²[R] ≠ 0 := sorry_proof
  fun_prop (disch:=aesop)


-- TODO: how can we streamline writing all of these theorems?

@[fun_trans]
theorem norm₂.arg_x.fderiv_rule_at (x : U) (hx : x ≠ 0) :
    fderiv R (fun x : U => ‖x‖₂[R]) x
    =
    fun dx =>L[R] ⟪dx,x⟫[R] / ‖x‖₂[R] := by
  have : ‖x‖₂²[R] ≠ 0 := sorry_proof
  conv_lhs => unfold norm₂
  fun_trans (disch:=assumption)
  ext dx; simp [norm₂]
  rw [mul_div_mul_left _ _ two_ne_zero]

@[fun_trans]
theorem norm₂.arg_x.fderiv_rule (f : X → U) (hf : Differentiable R f) (hf' : ∀ x, f x ≠ 0) :
    fderiv R (fun x => ‖f x‖₂[R])
    =
    fun x =>
      let y := f x
      fun dx =>L[R]
        let dy := fderiv R f x dx
        ⟪dy,y⟫[R] / ‖y‖₂[R] := by
  funext x; fun_trans (disch:=aesop)

@[fun_trans]
theorem norm₂.arg_x.fwdFDeriv_rule_at (x : U) (hx : x ≠ 0) :
    fwdFDeriv R (fun x : U => ‖x‖₂[R]) x
    =
    fun dx =>
      let y := ‖x‖₂[R]
      (y, ⟪dx,x⟫[R] / y) := by
  unfold fwdFDeriv; fun_trans (disch:=assumption)

@[fun_trans]
theorem norm₂.arg_x.fwdFDeriv_rule (f : X → U) (hf : Differentiable R f) (hf' : ∀ x, f x ≠ 0) :
    fwdFDeriv R (fun x => ‖f x‖₂[R])
    =
    fun x dx =>
      let ydy := fwdFDeriv R f x dx
      let yn := ‖ydy.1‖₂[R]
      (yn, ⟪ydy.2,ydy.1⟫[R] / yn) := by
  unfold fwdFDeriv; fun_trans (disch:=assumption)

@[fun_trans]
theorem norm₂.arg_x.revFDeriv_rule_at (x : U) (hx : x ≠ 0) :
    revFDeriv R (fun x : U => ‖x‖₂[R]) x
    =
    let y := ‖x‖₂[R]
    (y, fun dy => (y⁻¹ * dy) • x) := by
  unfold revFDeriv; fun_trans (disch:=assumption) [smul_smul]


@[fun_trans]
theorem norm₂.arg_x.revFDeriv_rule (f : U → V) (hf : Differentiable R f) (hf' : ∀ x, f x ≠ 0) :
    revFDeriv R (fun x : U => ‖f x‖₂[R])
    =
    fun x =>
      let ydf := revFDeriv R f x
      let y := ‖ydf.1‖₂[R]
      (y, fun dy => ydf.2 ((y⁻¹ * dy) • ydf.1)) := by
  funext x; fun_trans (disch:=apply hf')


theorem norm₂_nonneg (R) [RealScalar R] {X} [NormedAddCommGroup X] [AdjointSpace R X] (x : X) :
    0 ≤ ‖x‖₂²[R] := by
  sorry_proof
