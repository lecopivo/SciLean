module

public import SciLean.Analysis.Scalar.Basic
public import Mathlib.Analysis.Complex.Cardinality

/-!
# The laws of `Scalar` do not determine `exp 0`, `exp (x+y)`, `make 1 0`, ...

`Scalar R K` only relates its operations to `ℂ` through `toComplex : K → ℂ`, for example
`toComplex (exp x) = Complex.exp (toComplex x)`. `toComplex` is not required to be injective,
to map `0` to `0` or to be a ring homomorphism. So these laws don't pin down the value of
`exp x`, only the value of `toComplex (exp x)`.

This file makes that precise. `sectionScalar K f s` is a `Scalar ℝ K` instance for any map
`f : K → ℂ` with a right inverse `s`: each operation is computed in `ℂ` and brought back with
`s`. With this construction:

* `weirdComplexScalar : Scalar ℝ ℂ` uses `f z = z ^ 2` and `s w = -(w ^ (1/2))`. In it
  `exp 0 = -1`.
* `weirdRealScalar : RealScalar ℝ` uses a bijection `ℝ ≃ ℂ` as `f`.

Together they show that the following `sorry_proof` lemmas can't be derived from the class laws.
Each fails in an honest model of the classes, built with standard axioms only:

* `exp_zero` and `exp_add` in `SciLean/AD/Rules/Exp.lean`
* `scalar_make_one` and `Scalar.toReal_ofReal` in `SciLean/Analysis/Scalar/Basic.lean`

This file is not imported by `SciLean.lean`.
-/

@[expose] public section

namespace SciLean.ScalarLawsIndependence

open Classical

/-- A `Scalar ℝ K` structure on any `RCLike K`, given `f : K → ℂ` (used as `toComplex`)
with a right inverse `s`. Every operation is computed in `ℂ` and mapped back by `s`, so all
the `*_def` laws hold because `f (s w) = w`. `toReal` is the identity, and `ofReal` is the
constant `0` (the class states no law for it). -/
@[instance_reducible]
noncomputable def sectionScalar (K : Type) [inst : RCLike K] (f : K → ℂ) (s : ℂ → K)
    (hfs : ∀ w, f (s w) = w) : Scalar ℝ K where
  toRCLike := inst
  toComplex := f
  toReal := id
  ofReal := fun _ => 0
  ofComplex := s
  make x y := if ∀ y : K, RCLike.im y = 0 then s ⟨x, 0⟩ else s ⟨x, y⟩
  make_def x y := by split_ifs <;> simp [hfs]
  real x := (f x).re
  real_def _ := rfl
  imag x := (f x).im
  imag_def _ := rfl
  sin x := s (Complex.sin (f x))
  sin_def _ := hfs _
  cos x := s (Complex.cos (f x))
  cos_def _ := hfs _
  tan x := s (Complex.tan (f x))
  tan_def _ := hfs _
  tanh x := s (Complex.tanh (f x))
  tanh_def _ := hfs _
  exp x := s (Complex.exp (f x))
  exp_def _ := hfs _
  log x := s (Complex.log (f x))
  log_def _ := hfs _
  sqrt x := if ∀ y : K, RCLike.im y = 0 then s (Real.sqrt (f x).re) else s ((f x).cpow (1/2))
  sqrt_def x := by split_ifs <;> simp [hfs]
  pow x y := s (f x ^ f y)
  pow_def x y := by split_ifs <;> simp [hfs]
  abs x := ‖f x‖
  abs_def _ := rfl
  tgamma x := s (Complex.Gamma (f x))
  tgamma_def _ := hfs _
  lgamma x := Real.log ‖Complex.Gamma (f x)‖
  lgamma_def _ := rfl
  isFinite _ := true
  isNaN _ := false
  isInf _ := false

/-- The square of the chosen right inverse is the identity: `(-(w ^ (1/2))) ^ 2 = w`. -/
theorem neg_sqrt_sq (w : ℂ) : (-(w ^ (1/2 : ℂ))) ^ 2 = w := by
  rw [neg_sq]
  have := Complex.cpow_ofNat_inv_pow w 2
  simp only [one_div] at this ⊢
  exact this

/-- A `Scalar ℝ ℂ` structure with `toComplex z = z ^ 2`, whose operations use the negative
square root to come back from `ℂ`. It satisfies every law of `Scalar`. -/
@[instance_reducible]
noncomputable def weirdComplexScalar : Scalar ℝ ℂ :=
  sectionScalar ℂ (fun z => z ^ 2) (fun w => -(w ^ (1/2 : ℂ))) neg_sqrt_sq

/-- A bijection between `ℝ` and `ℂ` (they have the same cardinality). -/
noncomputable def realEquivComplex : ℝ ≃ ℂ :=
  (Cardinal.eq.1 (Cardinal.mk_real.trans Cardinal.mk_complex.symm)).some

/-- A `RealScalar ℝ` structure whose `toComplex` is a bijection `ℝ ≃ ℂ`. It satisfies every
law of `RealScalar`. It only serves to show that the hypothesis `[RealScalar R]` of the lemmas
below can be met without `sorry`. -/
@[instance_reducible]
noncomputable def weirdRealScalar : RealScalar ℝ where
  toScalar := sectionScalar ℝ realEquivComplex realEquivComplex.symm
    realEquivComplex.apply_symm_apply
  order := inferInstance
  is_real _ := rfl
  asin x := Real.arcsin x
  asin_def _ := rfl
  acos x := Real.arccos x
  acos_def _ := rfl
  atan x := Real.arctan x
  atan_def _ := rfl

theorem weirdComplexScalar_exp_zero : @Scalar.exp ℝ ℂ weirdComplexScalar 0 = -1 := by
  change -((Complex.exp (0 ^ 2)) ^ (1/2 : ℂ)) = -1
  simp

theorem weirdComplexScalar_make_one_zero : @Scalar.make ℝ ℂ weirdComplexScalar 1 0 = -1 := by
  have h : ¬ ∀ y : ℂ, RCLike.im y = 0 := fun h => by simpa using h Complex.I
  change (if ∀ y : ℂ, RCLike.im y = 0 then _ else _) = _
  simp only [h, ↓reduceIte]
  change -((⟨1, 0⟩ : ℂ) ^ (1/2 : ℂ)) = -1
  rw [show (⟨1, 0⟩ : ℂ) = 1 from rfl]
  simp

/-- `exp_zero` (`SciLean/AD/Rules/Exp.lean`) does not follow from the laws of `RealScalar` and
`Scalar`: there are lawful instances with `exp 0 ≠ 1`. -/
theorem exp_zero_not_derivable :
    ¬ ∀ (R C : Type) [RealScalar R] [Scalar R C], Scalar.exp (0 : C) = 1 := by
  intro h
  have := @h ℝ ℂ weirdRealScalar weirdComplexScalar
  change @Scalar.exp ℝ ℂ weirdComplexScalar (0 : ℂ) = (1 : ℂ) at this
  rw [weirdComplexScalar_exp_zero] at this
  norm_num at this

/-- `exp_add` (`SciLean/AD/Rules/Exp.lean`) does not follow from the laws of `RealScalar` and
`Scalar`: in `weirdComplexScalar`, `exp (0 + 0) = -1` but `exp 0 * exp 0 = 1`. -/
theorem exp_add_not_derivable :
    ¬ ∀ (R C : Type) [RealScalar R] [Scalar R C] (x y : C),
      Scalar.exp (x + y) = Scalar.exp x * Scalar.exp y := by
  intro h
  have := @h ℝ ℂ weirdRealScalar weirdComplexScalar 0 0
  change @Scalar.exp ℝ ℂ weirdComplexScalar ((0 : ℂ) + 0) = @Scalar.exp ℝ ℂ weirdComplexScalar 0 * @Scalar.exp ℝ ℂ weirdComplexScalar 0 at this
  rw [add_zero, weirdComplexScalar_exp_zero] at this
  norm_num at this

/-- `scalar_make_one` (`SciLean/Analysis/Scalar/Basic.lean`) does not follow from the laws of
`RealScalar` and `Scalar`: in `weirdComplexScalar`, `make 1 0 = -1`. -/
theorem scalar_make_one_not_derivable :
    ¬ ∀ (R K : Type) [RealScalar R] [Scalar R K], Scalar.make (1 : R) 0 = (1 : K) := by
  intro h
  have := @h ℝ ℂ weirdRealScalar weirdComplexScalar
  change @Scalar.make ℝ ℂ weirdComplexScalar (1 : ℝ) 0 = (1 : ℂ) at this
  rw [weirdComplexScalar_make_one_zero] at this
  norm_num at this

/-- `Scalar.toReal_ofReal` (`SciLean/Analysis/Scalar/Basic.lean`) does not follow from the laws
of `Scalar`: the class states no law for `ofReal`, and in `weirdComplexScalar` it is `0`. -/
theorem toReal_ofReal_not_derivable :
    ¬ ∀ (R K : Type) [Scalar R K] (x : ℝ), Scalar.toReal (K:=K) (Scalar.ofReal (K:=K) x) = x := by
  intro h
  have := @h ℝ ℂ weirdComplexScalar 1
  exact zero_ne_one this

end SciLean.ScalarLawsIndependence
