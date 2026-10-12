module

public import SciLean.Analysis.AdjointSpace.Adjoint
public import SciLean.Analysis.Calculus.FDeriv
public import SciLean.Algebra.Determinant
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section


open Module

namespace SciLean

set_option linter.unusedVariables false

set_option deprecated.oldSectionVars true

variable
  {R} [RealScalar R]
  {U} [NormedAddCommGroup U] [AdjointSpace R U] [CompleteSpace U]
  {V} [NormedAddCommGroup V] [AdjointSpace R V] [CompleteSpace V]
  {W} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]


variable (R)
@[fun_trans]
noncomputable
def jacobian (g : U → V) (x : U) : R :=
  let dg := fderiv R g x
  let dg' :=  adjoint R dg
  Scalar.sqrt (det R (dg' ∘ dg))

variable {R}


@[fun_trans]
theorem jacobian.id_rule :
    jacobian R (fun x : U => x)
    =
    fun _ => 1 := by
  funext x
  show Scalar.sqrt
    (det R ((adjoint R ⇑(fderiv R (fun x : U => x) x)) ∘ ⇑(fderiv R (fun x : U => x) x))) = 1
  rw [fderiv_fun_id]
  show Scalar.sqrt (det R ((adjoint R (fun x : U => x)) ∘ (fun x : U => x))) = 1
  rw [adjoint.adjoint_id]
  rw [show ((fun x : U => x) ∘ (fun x : U => x)) = (fun x : U => x) from rfl]
  rw [det.id_rule]
  -- note: `scalar_sqrt_one` is itself still assumed in `SciLean/Analysis/Scalar/Basic.lean`
  exact scalar_sqrt_one


@[fun_trans]
theorem jacobian.const_rule (y : V) :
    jacobian R (fun (_ : U) => y)
    =
    fun _ => if finrank R U = 0 then 1 else 0 := by
  funext x
  show Scalar.sqrt
    (det R ((adjoint R ⇑(fderiv R (fun _ : U => y) x)) ∘ ⇑(fderiv R (fun _ : U => y) x))) = _
  rw [fderiv_fun_const]
  simp only [Pi.zero_apply]
  rw [show ⇑(0 : U →L[R] V) = fun _ : U => (0:V) from rfl, adjoint.const_rule,
      show ((fun _ : V => (0:U)) ∘ (fun _ : U => (0:V))) = fun _ : U => (0:U) from rfl]
  have hlin : IsLinearMap R (fun _ : U => (0:U)) := by
    constructor <;> intros <;> simp
  have hmk : IsLinearMap.mk' (fun _ : U => (0:U)) hlin = 0 := by ext x; rfl
  have hdet : det R (fun _ : U => (0:U)) = if finrank R U = 0 then 1 else 0 := by
    simp only [det, hlin, ↓reduceDIte, hmk, LinearMap.det_zero]
    by_cases h : finrank R U = 0 <;> simp [h, zero_pow]
  rw [hdet]
  -- note: the final step uses `scalar_sqrt_one` and `scalar_sqrt_zero` which are themselves
  -- still assumed in `SciLean/Analysis/Scalar/Basic.lean`
  by_cases h : finrank R U = 0 <;> simp [h]


-- note: as stated this is false, the chain rule gives `jacobian R f (g x)` instead of
-- `jacobian R f x` (e.g. `g x = x + 1`, `f x = x^2` on `ℝ`)
@[fun_trans]
theorem jacobian.comp_rule (f : U → V) (g : U → U)
    (hf : Differentiable R f) (hg : Differentiable R g) :
    jacobian R (fun x => f (g x))
    =
    fun x => jacobian R f x * jacobian R g x := by sorry_proof


open FiniteDimensional in
@[fun_trans]
theorem HSMul.hSMul.arg_x.jacobian_rule
    (r : R) (f : U → V) (hf : Differentiable R f)  :
    jacobian R (fun x => r • f x)
    =
    fun x =>
      (Scalar.abs r)^(finrank R U) • jacobian R f x := by
  funext x
  have hd : fderiv R (fun x => r • f x) x = r • fderiv R f x := fderiv_const_smul (hf x) r
  unfold jacobian
  simp only
  rw [hd]
  set L := fderiv R f x
  have hL : IsContinuousLinearMap R (fun y => L y) := by fun_prop
  have ha : adjoint R ⇑(r • L) = fun y => r • adjoint R (fun y => L y) y := by
    rw [show ⇑(r • L) = fun y => r • L y from rfl, HSMul.hSMul.arg_a1.adjoint_rule r _ hL,
      conj_for_real_scalar]
  have hA : IsLinearMap R (fun y => adjoint R (fun y => L y) y) := adjoint.arg_y.IsLinearMap _
  have hcomp : (adjoint R ⇑(r • L) ∘ ⇑(r • L)) = fun y => (r*r) • (adjoint R ⇑L ∘ ⇑L) y := by
    rw [ha]; funext y
    simp only [Function.comp, FunLike.coe_smul, Pi.smul_apply]
    rw [hA.map_smul, smul_smul]
  have hlin : IsLinearMap R (adjoint R ⇑L ∘ ⇑L) := by
    constructor
    · intro a b; simp [Function.comp, hA.map_add]
    · intro c a; simp [Function.comp, hA.map_smul]
  have hlin2 : IsLinearMap R (fun y => (r*r) • (adjoint R ⇑L ∘ ⇑L) y) := by
    constructor
    · intro a b; rw [hlin.map_add, smul_add]
    · intro c a; rw [hlin.map_smul, smul_comm]
  -- `det (c • A) = c ^ finrank * det A`
  have hdet : det R (fun y => (r*r) • (adjoint R ⇑L ∘ ⇑L) y)
      = (r*r)^(finrank R U) * det R (adjoint R ⇑L ∘ ⇑L) := by
    simp only [det, hlin, hlin2, ↓reduceDIte]
    rw [show IsLinearMap.mk' (fun y => (r*r) • (adjoint R ⇑L ∘ ⇑L) y) hlin2
      = (r*r) • IsLinearMap.mk' _ hlin from rfl, LinearMap.det_smul]
  rw [hcomp, hdet]
  generalize det R (adjoint R ⇑L ∘ ⇑L) = d
  generalize finrank R U = n
  -- `√((r*r)^n * d) = |r|^n * √d`, computed in `ℝ` through `Scalar.toReal`
  apply Scalar.toReal_injective
  have hsqrt : ∀ z : R, Scalar.toReal R (Scalar.sqrt z) = Real.sqrt (Scalar.toReal R z) := by
    intro z
    have h := Scalar.sqrt_def (K:=R) z
    simpa only [RealScalar.is_real, implies_true, ↓reduceIte, Scalar.toComplex_eq_toReal,
      RCLike.re_to_complex, Complex.ofReal_re] using h
  have habs : Scalar.toReal R (Scalar.abs r) = |Scalar.toReal R r| := by
    rw [Scalar.abs_def, Scalar.toComplex_eq_toReal, Complex.norm_real, Real.norm_eq_abs]
  have hpow : ∀ (z : R) (m : ℕ), Scalar.toReal R (z ^ m) = Scalar.toReal R z ^ m := by
    intro z m
    conv_lhs => rw [← Scalar.algebraMap_toReal z, ← map_pow, Scalar.toReal_algebraMap]
  rw [smul_eq_mul, Scalar.toReal_mul, hsqrt, hsqrt, Scalar.toReal_mul, hpow, hpow,
    Scalar.toReal_mul, habs, ← abs_mul_abs_self (Scalar.toReal R r), mul_pow, ← sq,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (abs_nonneg _) _)]


open Matrix in
/-- The Gram matrix `⟪w i, w j⟫` of finitely many vectors has nonnegative determinant. -/
private theorem gram_det_nonneg {ι} [Fintype ι] [DecidableEq ι] {Y} [NormedAddCommGroup Y] [AdjointSpace R Y] (w : ι → Y) :
   0 ≤ Scalar.toReal R (Matrix.of fun i j => @inner R Y _ (w i) (w j)).det := by
  let T : R →+* ℝ :=
    { toFun := Scalar.toReal R
      map_one' := Scalar.toReal_one
      map_mul' := Scalar.toReal_mul
      map_zero' := Scalar.toReal_zero
      map_add' := fun x y => by
        rw [← Scalar.algebraMap_toReal x, ← Scalar.algebraMap_toReal y, ← map_add,
          Scalar.toReal_algebraMap, Scalar.toReal_algebraMap, Scalar.toReal_algebraMap] }
  have hT : ∀ z, T z = Scalar.toReal R z := fun _ => rfl
  have hre : ∀ z : R, Scalar.toReal R z = RCLike.re z := by
    intro z
    conv_rhs => rw [← Scalar.algebraMap_toReal z]
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re]
  rw [← hT, RingHom.map_det]
  apply Matrix.PosSemidef.det_nonneg
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, star_trivial, hT]
    rw [← AdjointSpace.inner_conj_symm, conj_for_real_scalar]
  · intro x
    let y := ∑ i, algebraMap ℝ R (x i) • w i
    have hy : star x ⬝ᵥ (T.mapMatrix (Matrix.of fun i j => @inner R Y _ (w i) (w j)) *ᵥ x) = RCLike.re (@inner R Y _ y y) := by
      rw [← hre, ← hT]
      simp only [y, AdjointSpace.sum_inner, AdjointSpace.inner_sum, AdjointSpace.inner_smul_left,
        AdjointSpace.inner_smul_right, conj_for_real_scalar, map_sum, map_mul,
        dotProduct, mulVec, star_trivial, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
      simp only [hT, Scalar.toReal_algebraMap]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hy]; exact AdjointSpace.inner_self_nonneg

/-- `det (B† ∘ B) ≥ 0`, shown through the Gram matrices of a basis `b` and of `B ∘ b`. -/
private theorem det_adjoint_comp_self_nonneg {Y} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
    (B : U → Y) (hB : IsContinuousLinearMap R B) :
    0 ≤ Scalar.toReal R (SciLean.det R (adjoint R B ∘ B)) := by
  have hA : IsLinearMap R (fun y => adjoint R B y) := adjoint.arg_y.IsLinearMap B
  have hl : IsLinearMap R (adjoint R B ∘ B) := by
    constructor
    · intro a b; simp [Function.comp, hB.linear.map_add, hA.map_add]
    · intro c a; simp [Function.comp, hB.linear.map_smul, hA.map_smul]
  simp only [SciLean.det, hl, ↓reduceDIte]
  by_cases hfin : Module.Finite R U
  swap
  · rw [LinearMap.det_eq_one_of_not_module_finite hfin, Scalar.toReal_one]; exact zero_le_one
  classical
  let b := Module.Free.chooseBasis R U
  rw [← LinearMap.det_toMatrix b]
  set N := LinearMap.toMatrix b b (IsLinearMap.mk' _ hl)
  let G : Matrix _ _ R := Matrix.of fun i j => @inner R U _ (b i) (b j)
  let P : Matrix _ _ R := Matrix.of fun i j => @inner R Y _ (B (b i)) (B (b j))
  have hexp : ∀ x : U, x = ∑ k, b.repr x k • b k := fun x => (b.sum_repr x).symm
  have hkey : G * N = P := by
    ext i j
    simp only [Matrix.mul_apply, G, P, Matrix.of_apply, N,
      LinearMap.toMatrix_apply, IsLinearMap.mk'_apply, Function.comp]
    have h2 : @inner R U _ (b i) (adjoint R B (B (b j)))
        = ∑ k, @inner R U _ (b i) (b k) * b.repr (adjoint R B (B (b j))) k := by
      conv_lhs => rw [hexp (adjoint R B (B (b j)))]
      rw [AdjointSpace.inner_sum]
      simp [AdjointSpace.inner_smul_right, mul_comm]
    rw [← h2, adjoint_inner_right _ hB]
  have hG : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv
    have hbi : ∀ i, @inner R U _ (b i) (∑ j, v j • b j) = 0 := by
      intro i
      have := congrFun hGv i
      rw [AdjointSpace.inner_sum]
      simpa [Matrix.mulVec, dotProduct, G, AdjointSpace.inner_smul_right, mul_comm] using this
    have hx : (∑ j, v j • b j) = 0 := by
      apply (AdjointSpace.inner_self_eq_zero (𝕜:=R)).1
      rw [AdjointSpace.sum_inner]
      simp [AdjointSpace.inner_smul_left, hbi]
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v hx i
  have hdet := congrArg (fun M => Scalar.toReal R (Matrix.det M)) hkey
  simp only [Matrix.det_mul, Scalar.toReal_mul] at hdet
  have hG0 : 0 < Scalar.toReal R G.det := by
    refine lt_of_le_of_ne (gram_det_nonneg _) (fun h => hG ?_)
    apply Scalar.toReal_injective
    rw [← h, Scalar.toReal_zero]
  have hP0 : 0 ≤ Scalar.toReal R P.det := gram_det_nonneg _
  rw [← hdet] at hP0
  exact (mul_nonneg_iff_of_pos_left hG0).1 hP0

open FiniteDimensional in
@[fun_trans]
theorem Prod.mk.arg_xy.jacobian_rule
    (f : U → V) (g : U → W) (hf : Differentiable R f) (hg : Differentiable R g) :
    jacobian R (fun x => (f x, g x))
    =
    fun x =>
      let Jf := fun dx => fderiv R f x dx
      let Jg := fun dx => fderiv R g x dx
      let Gf := fun dx => adjoint R Jf (Jf dx)
      let Gg := fun dx => adjoint R Jg (Jg dx)
      Scalar.sqrt (Scalar.abs (det R (fun dx => Gf dx + Gg dx))) := by
  funext x
  unfold jacobian
  simp only
  rw [DifferentiableAt.fderiv_prodMk (hf x) (hg x)]
  set L := fderiv R f x
  set M := fderiv R g x
  have hL : IsContinuousLinearMap R (fun y => L y) := by fun_prop
  have hM : IsContinuousLinearMap R (fun y => M y) := by fun_prop
  have hD : IsContinuousLinearMap R ⇑(L.prod M) := by
    show IsContinuousLinearMap R (fun y => (L y, M y)); fun_prop
  have ha : (fun yz : V × W => adjoint R (fun y => L y) yz.1 + adjoint R (fun y => M y) yz.2)
      = adjoint R ⇑(L.prod M) := by
    rw [eq_adjoint_iff _ _ hD]
    intro yz x
    rw [AdjointSpace.inner_add_left, adjoint_inner_left _ hL, adjoint_inner_left _ hM]
    rfl
  have hcomp : adjoint R ⇑(L.prod M) ∘ ⇑(L.prod M)
      = fun dx => adjoint R (fun y => L y) (L dx) + adjoint R (fun y => M y) (M dx) := by
    rw [← ha]; rfl
  have hnn := det_adjoint_comp_self_nonneg _ hD
  rw [hcomp] at hnn ⊢
  generalize SciLean.det R (fun dx => adjoint R (fun y => L y) (L dx) + adjoint R (fun y => M y) (M dx)) = d at hnn ⊢
  apply Scalar.toReal_injective
  have hsqrt : ∀ z : R, Scalar.toReal R (Scalar.sqrt z) = Real.sqrt (Scalar.toReal R z) := by
    intro z
    have h := Scalar.sqrt_def (K:=R) z
    simpa only [RealScalar.is_real, implies_true, ↓reduceIte, Scalar.toComplex_eq_toReal,
      RCLike.re_to_complex, Complex.ofReal_re] using h
  rw [hsqrt, hsqrt, Scalar.abs_def, Scalar.toComplex_eq_toReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnn]
