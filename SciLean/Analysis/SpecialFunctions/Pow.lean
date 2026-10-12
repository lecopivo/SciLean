module

public import SciLean.Analysis.Calculus.FwdFDeriv
public import SciLean.Analysis.Calculus.RevFDeriv

public import SciLean.Meta.GenerateFunProp

@[expose] public section


open ComplexConjugate

namespace SciLean.Scalar

variable
  {R} [RealScalar R]


----------------------------------------------------------------------------------------------------
-- Sqrt --------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section Normed

variable
  {W : Type _} [NormedAddCommGroup W] [NormedSpace R W]
  {U : Type _} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]


theorem sqrt_hasDerivAt (x : R) (hx : x ≠ 0) :
    HasDerivAt (fun y : R => Scalar.sqrt y) (1 / (2 * Scalar.sqrt x)) x := by
  have hre : ∀ y : R, ((RCLike.re y : ℝ) : R) = y := fun y => by
    have h := RCLike.re_add_im y
    rw [RealScalar.is_real y] at h
    simpa using h
  have htoRe : ∀ y : R, toReal R y = RCLike.re y := fun y => by
    conv_lhs => rw [← hre y, ← RCLike.algebraMap_eq_ofReal, Scalar.toReal_algebraMap]
  have hsq : ∀ y : R, Scalar.sqrt y = ((Real.sqrt (RCLike.re y) : ℝ) : R) := fun y => by
    apply Scalar.toReal_injective
    have h := Scalar.sqrt_def (K:=R) y
    simp only [RealScalar.is_real, implies_true, ↓reduceIte, Scalar.toComplex_eq_toReal,
      RCLike.re_to_complex, Complex.ofReal_re] at h
    rw [h, htoRe, htoRe, RCLike.ofReal_re]
  have hx' : RCLike.re x ≠ 0 := fun h => hx (by rw [← hre x, h, RCLike.ofReal_zero])
  have h1 := (Real.hasDerivAt_sqrt hx').hasFDerivAt.comp x (RCLike.reCLM (K:=R)).hasFDerivAt
  have h2 := (RCLike.ofRealCLM (K:=R)).hasFDerivAt.comp x h1
  rw [hasDerivAt_iff_isLittleO]
  have h3 := h2.isLittleO
  convert h3 using 2 with y
  have hre' : ∀ y : R, algebraMap ℝ R (RCLike.re y) = y := hre
  have hsq' : algebraMap ℝ R (Real.sqrt (RCLike.re x)) = Scalar.sqrt x := (hsq x).symm
  simp [hsq]
  rw [hre', hre', hsq', map_ofNat, ← hsq x]

set_option linter.unusedVariables false in
def_fun_prop with_transitive (x : R) (hx : x ≠ 0) :
    DifferentiableAt R (fun x : R => sqrt x) x by exact (sqrt_hasDerivAt x hx).differentiableAt

set_option linter.unusedVariables false in
def_fun_prop with_transitive (x : W → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
    Differentiable R (fun w => sqrt (x w)) by
  intro w; fun_prop (disch := apply hx')

set_option linter.unusedVariables false in
@[fun_trans]
theorem sqrt.arg_x.fderiv_rule (x : R) (hx : x ≠ 0) :
  fderiv R sqrt x
  =
  let y := sqrt x
  fun dx =>L[R]
    dx/(2*y) := by
  rw [(sqrt_hasDerivAt x hx).hasFDerivAt.fderiv]
  ext; simp [div_eq_mul_inv]

set_option linter.unusedVariables false in
@[fun_trans]
theorem sqrt.arg_x.fderiv_rule' (x : W → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
  fderiv R (fun w => sqrt (x w))
  =
  fun w =>
    let y := sqrt (x w)
    fun dw =>L[R]
      let dx := fderiv R x w dw
      dx/(2*y) := by
  funext w
  fun_trans (disch:=apply hx')

@[fun_trans]
theorem sqrt.arg_x.fwdFDeriv_rule (x : R) (hx : x ≠ 0) :
  fwdFDeriv R sqrt x
  =
  let y := sqrt x
  fun dx =>
    (y,dx/(2*y)) := by unfold fwdFDeriv; fun_trans (disch:=assumption)

@[fun_trans]
theorem sqrt.arg_x.fwdFDeriv_rule' (x : W → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
  fwdFDeriv R (fun w => sqrt (x w))
  =
  fun w dw =>
    let xdx := fwdFDeriv R x w dw
    let y := sqrt (xdx.1)
    (y,xdx.2/(2*y)) := by
  funext w
  unfold fwdFDeriv
  fun_trans (disch:=assumption)

@[fun_trans]
theorem sqrt.arg_x.revFDeriv_rule (x : R) (hx : x ≠ 0) :
  revFDeriv R sqrt x
  =
  let y := sqrt x
  (y, fun dx => dx/(2*y)) := by unfold revFDeriv; fun_trans (disch:=assumption); funext y; ring

@[fun_trans]
theorem sqrt.arg_x.revFDeriv_rule' (x : U → R) (hx : Differentiable R x) (hx' : ∀ w, x w ≠ 0) :
  revFDeriv R (fun w => sqrt (x w))
  =
  fun w =>
    let xdx := revFDeriv R x w
    let y := sqrt (xdx.1)
    (y,fun dx =>
      let dy := xdx.2 dx
      (2*y)⁻¹ • dy) := by
  funext w
  unfold revFDeriv
  fun_trans (disch:=assumption)


end Normed
