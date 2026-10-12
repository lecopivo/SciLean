module

public import SciLean.Analysis.Scalar.FloatAsReal

/-!
# `sorry_proof`s in `FloatAsReal.lean` whose goals are false

Each theorem here is the negation of the goal of a `sorry_proof` in
`SciLean/Analysis/Scalar/FloatAsReal.lean`. Sections 1 and 2 are the two goals for which `try?`
answered `impossible by …`; section 3 covers the other false goals in that file.

In Lean 4.34 `Float` is a structure over a model that the kernel can evaluate, and the core
instance `instDecidableEqFloat` decides equality in that model, so `decide` works below.

The statements about `Float` alone (`no_field_with_sciLean_inv`, `panic_one_ne_one` and the
IEEE group of section 3) depend on the standard axioms only.
The statements that mention the project's instances (`Field.qsmul`, `dist`, `‖·‖`, `RCLike.re`,
`Scalar.cos`, ...) inherit the axioms contained in those instances' definitions
(`sorryProofAxiom` and the `isomorph_rule_FloatToReal` axioms), so `#print axioms` lists them,
although the proofs themselves are `decide`, `rfl` and standard lemmas.
-/

@[expose] public section

namespace SciLean.FloatAsRealFalseGoals

/-- `1 / 0` is not `0` for floats (it is `inf`). -/
theorem one_div_zero_ne_zero : ¬ ((1.0 / 0 : Float) = 0) := by
  decide

/-! ## 1. `inv_zero` in `instance : Field Float`

`FloatAsReal.lean`, line `inv_zero := sorry_proof`. -/

/-- No `Field Float` structure can use SciLean's inverse `x ↦ 1 / x` together with the float
`0`: the field axiom `inv_zero` would say `1 / 0 = 0`. -/
theorem no_field_with_sciLean_inv (F : Field Float) (hinv : ∀ x : Float, F.inv x = 1.0 / x)
    (hzero : F.zero = (0 : Float)) : False := by
  have h := F.inv_zero
  change F.inv F.zero = F.zero at h
  rw [hinv, hzero] at h
  exact one_div_zero_ne_zero h

/-- The project's `Field Float` instance uses exactly that inverse. -/
theorem instFieldFloat_inv (x : Float) : instFieldFloat_sciLean.inv x = 1.0 / x := rfl

/-- The project's `Field Float` instance uses the float `0`. -/
theorem instFieldFloat_zero : instFieldFloat_sciLean.zero = (0 : Float) := rfl

/-- Hence the goal of `inv_zero := sorry_proof` in the project's `Field Float` instance is false. -/
theorem instFieldFloat_inv_zero_goal_false :
    ¬ (instFieldFloat_sciLean.inv instFieldFloat_sciLean.zero = instFieldFloat_sciLean.zero) := by
  rw [instFieldFloat_inv, instFieldFloat_zero]
  exact one_div_zero_ne_zero

/-! ## 2. `map_one'` in `algebraMap` of `instance : Algebra ℝ Float`

`algebraMap := ⟨⟨⟨fun r => realToFloat r, sorry_proof⟩, …⟩, …⟩`: the `sorry_proof` has goal
`realToFloat 1 = 1`. The map `ℝ → Float` behind `realToFloat` is `panic! "…"`, whose logical
value is `default`, i.e. the constant `0`. -/

/-- A panicking function `ℝ → Float` does not send `1` to `1`. -/
theorem panic_one_ne_one (msg : String) : (panic msg : ℝ → Float) 1 ≠ 1 := by
  change (default : Float) ≠ 1
  decide

/-- `realToFloat` is the constant `default` (`0`). -/
theorem realToFloat_eq_default (r : ℝ) : realToFloat r = default := rfl

/-- Hence the goal `realToFloat 1 = 1` of that `sorry_proof` is false. -/
theorem realToFloat_one_ne_one : realToFloat 1 ≠ 1 := by
  rw [realToFloat_eq_default]
  exact panic_one_ne_one ""

/-! ## 3. Other `sorry_proof`s in `FloatAsReal.lean` whose goals are false

Each theorem below is the negation of the goal of one `sorry_proof` field. The first group
is about IEEE floats only (`NaN`, `-0`, `inf`, rounding and overflow) and is checked by
`decide` in Lean's float model. The second group uses that `floatToReal` and `realToFloat` are
`panic!`, so the norm, distance, `re` and `toComplex` of every float are `0` and `ofReal` is
constant. Not covered: `npow_succ`, `zpow_succ'` and `zpow_neg'` (SciLean's `Float.npow` and
`Float.zpow` are `partial`, hence opaque). `sub_eq_add_neg` and `zsmul_neg'` are true for IEEE
floats and are proved in `FloatAsReal.lean`. -/

/-- `NaN`. -/
abbrev nan' : Float := 0 / 0
/-- `+inf`. -/
abbrev inf' : Float := 1 / 0
/-- `2^53`: from here on, consecutive floats are `2` apart. -/
abbrev two53 : Float := Float.ofNat (2 ^ 53)
/-- `2^636` (`= (2^53)^12`): its square overflows to `inf`. -/
abbrev big : Float :=
  two53 * two53 * two53 * two53 * two53 * two53 * two53 * two53 * two53 * two53 * two53 * two53

/-! ### IEEE floats (`LinearOrder`, `CommRing`, `Field`, `IsStrictOrderedRing`) -/

/-- `le_refl` is false: `NaN ≤ NaN` fails. -/
theorem le_refl_false : ¬ ∀ x : Float, x ≤ x := fun h => absurd (h nan') (by decide)

/-- `le_antisymm` is false: `-0 ≤ 0` and `0 ≤ -0`, but `-0 ≠ 0`. -/
theorem le_antisymm_false : ¬ ∀ a b : Float, a ≤ b → b ≤ a → a = b :=
  fun h => absurd (h (-0) 0 (by decide) (by decide)) (by decide)

/-- `le_total` is false: `NaN` is not comparable with itself. -/
theorem le_total_false : ¬ ∀ a b : Float, a ≤ b ∨ b ≤ a := fun h => absurd (h nan' nan') (by decide)

/-- `add_assoc` is false because of rounding. -/
theorem add_assoc_false : ¬ ∀ a b c : Float, a + b + c = a + (b + c) :=
  fun h => absurd (h two53 1 1) (by decide)

/-- `mul_assoc` is false because of overflow. -/
theorem mul_assoc_false : ¬ ∀ a b c : Float, a * b * c = a * (b * c) :=
  fun h => absurd (h big big (1 / big)) (by decide +kernel)

/-- `add_zero` is false: `-0 + 0 = 0`. -/
theorem add_zero_false : ¬ ∀ a : Float, a + 0 = a := fun h => absurd (h (-0)) (by decide)

/-- `zero_add` is false: `0 + -0 = 0`. -/
theorem zero_add_false : ¬ ∀ a : Float, 0 + a = a := fun h => absurd (h (-0)) (by decide)

/-- `neg_add_cancel` is false: `-inf + inf = NaN`. -/
theorem neg_add_cancel_false : ¬ ∀ a : Float, -a + a = 0 := fun h => absurd (h inf') (by decide)

/-- `nsmul_zero` is false (`nsmul n x := n.toFloat * x`): `0 * inf = NaN`. -/
theorem nsmul_zero_false : ¬ ∀ x : Float, (0 : ℕ).toFloat * x = 0 :=
  fun h => absurd (h inf') (by decide)

/-- `nsmul_succ` is false: `1 * inf = inf` but `0 * inf + inf = NaN`. -/
theorem nsmul_succ_false : ¬ ∀ (n : ℕ) (x : Float), (n + 1).toFloat * x = n.toFloat * x + x :=
  fun h => absurd (h 0 inf') (by decide)

/-- `zsmul_zero'` is false (`zsmul n x := Float.ofInt n * x`): `0 * inf = NaN`. -/
theorem zsmul_zero_false : ¬ ∀ x : Float, Float.ofInt 0 * x = 0 :=
  fun h => absurd (h inf') (by decide)

/-- `zsmul_succ'` is false: `1 * inf = inf` but `0 * inf + inf = NaN`. -/
theorem zsmul_succ_false :
    ¬ ∀ (n : ℕ) (x : Float), Float.ofInt (n.succ : ℤ) * x = Float.ofInt (n : ℤ) * x + x :=
  fun h => absurd (h 0 inf') (by decide)

/-- `natCast_succ` is false (`natCast n := n.toUInt64.toFloat`): `UInt64` wraps around. -/
theorem natCast_succ_false :
    ¬ ∀ n : ℕ, (n + 1).toUInt64.toFloat = n.toUInt64.toFloat + 1 :=
  fun h => absurd (h (2 ^ 64 - 1)) (by decide)

/-- `npow_succ` is false (`npow n x := x.npow n`, and `x.npow 4 = x*x*(x*x)`): with rounding,
`x*x*(x*x) ≠ x*x*x*x` for `x = 1.005`. -/
theorem npow_succ_false : ¬ ∀ (n : ℕ) (x : Float), x.npow (n + 1) = x.npow n * x :=
  fun h => absurd (h 3 1.005) (by decide)

/-- `zpow_succ'` is false (`zpow n x := x.zpow n`), for the same reason as `npow_succ`. -/
theorem zpow_succ_false :
    ¬ ∀ (n : ℕ) (x : Float), x.zpow (n.succ : ℤ) = x.zpow (n : ℤ) * x :=
  fun h => absurd (h 3 1.005) (by decide)

/-- `zpow_neg'` is false (the inverse is `1 / x`): `(1/x)*(1/x) ≠ 1/(x*x)` for `x = 1.002`. -/
theorem zpow_neg_false :
    ¬ ∀ (n : ℕ) (x : Float), x.zpow (Int.negSucc n) = 1.0 / x.zpow (n.succ : ℤ) :=
  fun h => absurd (h 1 1.002) (by decide)

/-- `div_eq_mul_inv` is false (the inverse is `1 / x`): `49 / 49 = 1` but
`49 * (1 / 49) < 1`. -/
theorem div_eq_mul_inv_false : ¬ ∀ a b : Float, a / b = a * (1.0 / b) :=
  fun h => absurd (h 49 49) (by decide)

/-- `mul_inv_cancel` is false: `49 * (1 / 49) ≠ 1`. -/
theorem mul_inv_cancel_false : ¬ ∀ a : Float, a ≠ 0 → a * (1.0 / a) = 1 :=
  fun h => absurd (h 49 (by decide)) (by decide)

/-- The rational number `1 / 49`, written with its numerator and denominator. -/
def q49 : ℚ := ⟨1, 49, by decide, by decide⟩

/-- `qsmul_def` is false for the project's `Field Float`: `(1 * 49) / 49 = 1` but
`(1 / 49) * 49 ≠ 1`. -/
theorem qsmul_def_false : ¬ ∀ (q : ℚ) (x : Float), Field.qsmul q x = (q : Float) * x :=
  fun h => absurd (h q49 49) (by decide)

/-- `nnqsmul_def` is false for the project's `Field Float`, for the same reason. -/
theorem nnqsmul_def_false : ¬ ∀ (q : ℚ≥0) (x : Float), Field.nnqsmul q x = (q : Float) * x :=
  fun h => absurd (h ⟨q49, by decide⟩ 49) (by decide)

/-- `add_le_add_left` is false: `NaN + c ≤ NaN + c` fails. -/
theorem add_le_add_left_false : ¬ ∀ a b : Float, a ≤ b → ∀ c : Float, a + c ≤ b + c :=
  fun h => absurd (h 0 0 (by decide) nan') (by decide)

/-- `le_of_add_le_add_left` is false: `inf + 1 ≤ inf + 0` but not `1 ≤ 0`. -/
theorem le_of_add_le_add_left_false : ¬ ∀ a b c : Float, a + b ≤ a + c → b ≤ c :=
  fun h => absurd (h inf' 1 0 (by decide)) (by decide)

/-- `mul_lt_mul_of_pos_left` is false: `1 < 2` but `inf * 1 = inf * 2`. -/
theorem mul_lt_mul_of_pos_left_false :
    ¬ ∀ a : Float, 0 < a → ∀ b c : Float, b < c → a * b < a * c :=
  fun h => absurd (h inf' (by decide) 1 2 (by decide)) (by decide)

/-- `mul_lt_mul_of_pos_right` is false: `1 < 2` but `1 * inf = 2 * inf`. -/
theorem mul_lt_mul_of_pos_right_false :
    ¬ ∀ c : Float, 0 < c → ∀ a b : Float, a < b → a * c < b * c :=
  fun h => absurd (h inf' (by decide) 1 2 (by decide)) (by decide)

/-! ### Consequences of `floatToReal` and `realToFloat` being `panic!` -/

/-- `floatToReal` is logically the constant `0`. -/
theorem floatToReal_eq_zero (x : Float) : floatToReal x = 0 := rfl

/-- `eq_of_dist_eq_zero` is false: the distance of `0` and `1` is `0`. -/
theorem eq_of_dist_eq_zero_false : ¬ ∀ x y : Float, dist x y = 0 → x = y :=
  fun h => absurd (h 0 1 rfl) (by decide)

/-- `lt_norm_lt` is false: every norm is `0`, so no norm lies between `1` and `2`. -/
theorem lt_norm_lt_false :
    ¬ ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : Float, x < ‖a‖ ∧ ‖a‖ < y := by
  intro h
  obtain ⟨a, ha, -⟩ := h 1 2 zero_le_one one_lt_two
  have : ‖a‖ = 0 := floatToReal_eq_zero _
  linarith

/-- `re_add_im_ax` is false: `algebraMap ℝ Float` is constant, so the left side does not
depend on `z`. -/
theorem re_add_im_ax_false :
    ¬ ∀ z : Float,
      algebraMap ℝ Float (RCLike.re z) + algebraMap ℝ Float (RCLike.im z) * RCLike.I = z := by
  intro h
  have h0 := h 0
  have h1 := h 1
  change (default : Float) + default * 0 = 0 at h0
  change (default : Float) + default * 0 = 1 at h1
  exact absurd (h0.symm.trans h1) (by decide)

/-- `ofReal_re_ax` is false: `re` is `0` everywhere. -/
theorem ofReal_re_ax_false : ¬ ∀ r : ℝ, RCLike.re (algebraMap ℝ Float r) = r := by
  intro h
  have : (0 : ℝ) = 1 := h 1
  exact zero_ne_one this

/-- `le_iff_re_im` is false: `re` and `im` are `0` everywhere, but `1 ≤ 0` fails. -/
theorem le_iff_re_im_false :
    ¬ ∀ z w : Float, z ≤ w ↔ RCLike.re z ≤ RCLike.re w ∧ RCLike.im z = RCLike.im w := by
  intro h
  have : (1 : Float) ≤ 0 := (h 1 0).mpr ⟨le_refl (0 : ℝ), rfl⟩
  exact absurd this (by decide)

/-- `cos_def` of `RealScalar Float` is false: `toComplex` is `0`, and `cos 0 = 1`. -/
theorem cos_def_false :
    ¬ ∀ x : Float, Scalar.toComplex (Scalar.cos x) = Complex.cos (Scalar.toComplex x) := by
  intro h
  have : (0 : ℂ) = Complex.cos 0 := h 0
  rw [Complex.cos_zero] at this
  exact zero_ne_one this

/-- `exp_def` of `RealScalar Float` is false: `toComplex` is `0`, and `exp 0 = 1`. -/
theorem exp_def_false :
    ¬ ∀ x : Float, Scalar.toComplex (Scalar.exp x) = Complex.exp (Scalar.toComplex x) := by
  intro h
  have : (0 : ℂ) = Complex.exp 0 := h 0
  rw [Complex.exp_zero] at this
  exact zero_ne_one this

open Classical in
/-- `pow_def` of `RealScalar Float` is false: the left side is `0`, but `(0 : ℂ) ^ 0 = 1`. -/
theorem pow_def_false :
    ¬ ∀ x y : Float,
      if ∀ z : Float, RCLike.im z = 0 then
        Scalar.toReal Float (Scalar.real (Scalar.pow x y)) =
          ((Scalar.toComplex x) ^ (Scalar.toComplex y)).re
      else
        Scalar.toComplex (Scalar.pow x y) = Scalar.toComplex x ^ Scalar.toComplex y := by
  intro h
  have him : ∀ z : Float, RCLike.im z = 0 := fun _ => rfl
  have h00 := h 0 0
  simp only [him, forall_const, ↓reduceIte] at h00
  have : (0 : ℝ) = ((0 : ℂ) ^ (0 : ℂ)).re := h00
  simp at this

end SciLean.FloatAsRealFalseGoals
