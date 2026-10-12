module

public import SciLean.Analysis.Scalar.ScalarLawsIndependence
public import SciLean.Data.IndexType.Operations
public import SciLean.Data.Idx.Idx2

/-!
# Why some remaining `sorry_proof`s cannot be replaced by real proofs

Each theorem below shows that one `sorry_proof` goal is either false or does not follow from the
class laws as they are currently stated. All proofs use standard axioms only.

* `real_log_def_false`: the `log_def` field of `instance : RealScalar ℝ`
  (`SciLean/Analysis/Scalar/Basic.lean`) is false: it fails at `x = -1`.
* `scalar_sqrt_one_not_derivable`: `scalar_sqrt_one` (`SciLean/Analysis/Scalar/Basic.lean`)
  does not follow from the laws of `RealScalar`, because they never pin down `Scalar.sqrt` itself.
* `sum_eq_finset_sum_not_derivable`: `IndexType.sum_eq_finset_sum`
  (`SciLean/Data/IndexType/Operations.lean`) does not follow from the classes `IndexType` and
  `FoldM`, because `FoldM` has no law about what `forIn` computes.
* `idx2_invFun_bounds_false`: the bounds obligation `sorry_proof` in `Idx2.finEquiv.invFun` and
  `Fin.toIdx2` (`SciLean/Data/Idx/Idx2.lean`) is false, because of `Int64` overflow.

This file is not imported by `SciLean.lean`.
-/

@[expose] public section

namespace SciLean.SorryProofObstructions

open ScalarLawsIndependence Classical

/-! ## `log_def` for `RealScalar ℝ` -/

/-- The `log_def` field of `instance : RealScalar ℝ` asks for
`toComplex (log x) = Complex.log (toComplex x)` with `toComplex x = ⟨x, 0⟩` and
`log x = Real.log x`. This is false: at `x = -1` the left side is `0` and the right side is `π i`. -/
theorem real_log_def_false :
    ¬ ∀ x : ℝ, (⟨Real.log x, 0⟩ : ℂ) = Complex.log ⟨x, 0⟩ := by
  intro h
  have h1 := congrArg Complex.im (h (-1))
  rw [show (⟨-1, 0⟩ : ℂ) = -1 from Complex.ext (by simp) (by simp), Complex.log_neg_one] at h1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
    mul_one, mul_zero, add_zero] at h1
  exact Real.pi_ne_zero h1.symm

/-- The same statement, phrased with the operations of the library's `instance : RealScalar ℝ`.
It is exactly the type of that instance's `log_def` field. `#print axioms` lists
`sorryProofAxiom` here only because the statement mentions the instance, whose `log_def` field is
the `sorry_proof` in question; the proof itself is `real_log_def_false`. -/
theorem realScalar_log_def_false :
    ¬ ∀ x : ℝ, Scalar.toComplex (Scalar.log x) = Complex.log (Scalar.toComplex x) :=
  real_log_def_false

/-! ## `scalar_sqrt_one` -/

/-- A bijection `ℝ ≃ ℂ` that sends `1` to `4`. -/
noncomputable def equivOneToFour : ℝ ≃ ℂ :=
  realEquivComplex.trans (Equiv.swap (realEquivComplex 1) 4)

theorem equivOneToFour_one : equivOneToFour 1 = 4 := by
  simp [equivOneToFour, Equiv.swap_apply_left]

/-- A lawful `RealScalar ℝ` structure whose `toComplex` is `equivOneToFour`. Its square root is
`sqrt x = toComplex⁻¹ (Real.sqrt (toComplex x).re)`, so `sqrt 1 = toComplex⁻¹ 2 ≠ 1`. -/
@[instance_reducible]
noncomputable def sqrtRealScalar : RealScalar ℝ where
  toScalar := sectionScalar ℝ equivOneToFour equivOneToFour.symm equivOneToFour.apply_symm_apply
  order := inferInstance
  is_real _ := rfl
  asin x := Real.arcsin x
  asin_def _ := rfl
  acos x := Real.arccos x
  acos_def _ := rfl
  atan x := Real.arctan x
  atan_def _ := rfl

theorem sqrtRealScalar_sqrt_one_ne_one : @Scalar.sqrt ℝ ℝ sqrtRealScalar.toScalar 1 ≠ 1 := by
  have hall : ∀ y : ℝ, RCLike.im y = 0 := fun _ => rfl
  change (if ∀ y : ℝ, RCLike.im y = 0 then _ else _) ≠ 1
  simp only [hall, implies_true, ↓reduceIte]
  intro h
  have h2 := congrArg equivOneToFour h
  rw [Equiv.apply_symm_apply, equivOneToFour_one, Complex.re_ofNat,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h2
  have h3 := congrArg Complex.re h2
  norm_num at h3

/-- `scalar_sqrt_one` (`SciLean/Analysis/Scalar/Basic.lean`) does not follow from the laws of
`RealScalar`: in the lawful instance `sqrtRealScalar`, `sqrt 1 ≠ 1`. The same instance shows that
lemmas about `sqrt` (its derivative, multiplicativity, ...) need more laws than the class has. -/
theorem scalar_sqrt_one_not_derivable :
    ¬ ∀ (R : Type) [RealScalar R], Scalar.sqrt (1 : R) = 1 :=
  fun h => sqrtRealScalar_sqrt_one_ne_one (@h ℝ sqrtRealScalar)

/-! ## `IndexType.sum_eq_finset_sum` -/

/-- A `FoldM` instance that ignores the loop body and returns the initial value. `FoldM` has no
laws, so this is a valid instance. -/
@[instance_reducible]
def skipFold (I : Type) : FoldM I Id where
  forIn _ init _ := pure init

/-- An `IndexType Unit 1` structure written out with explicit proofs (the library instance is
not used here because its construction depends on `sorry_proof`). -/
@[instance_reducible]
def unitIndexType : IndexType Unit 1 where
  toFintype := ⟨{()}, fun _ => Finset.mem_singleton_self _⟩
  toSize' := ⟨⟩
  toIdx _ := ⟨0, by decide⟩
  fromIdx _ := ()
  toFin _ := 0
  fromFin _ := ()
  toFin_eq_toIdx _ _ := rfl
  fromIdx_eq_fromFin _ := rfl
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

/-- `IndexType.sum_eq_finset_sum` (`SciLean/Data/IndexType/Operations.lean`) does not follow from
the classes `IndexType` and `FoldM`: with `skipFold`, `∑ᴵ i : Unit, 1 = 0` while the `Finset` sum
is `1`. -/
theorem sum_eq_finset_sum_not_derivable :
    ¬ ∀ (I : Type) (n : ℕ) [IndexType I n] [FoldM I Id] (f : I → ℕ),
      IndexType.sum f = Finset.univ.sum f := by
  intro h
  have h1 := @h Unit 1 unitIndexType (skipFold Unit) (fun _ => 1)
  change (0 : ℕ) = _ at h1
  simp at h1

/-! ## Bounds in `Idx2.finEquiv.invFun` and `Fin.toIdx2` -/

/-- `Idx2.finEquiv.invFun` and `Fin.toIdx2` build
`⟨x.1.toInt64 + a.toInt64, sorry_proof⟩ : Idx2 a b` from `x : Fin (b - a + 1).toNat`.
The bounds obligation is false: for `a = 2^63 - 1`, `b = 2^63` and `x = 1`, the `Int64` sum
overflows to `-2^63`, which is below `a`. -/
theorem idx2_invFun_bounds_false :
    ¬ ∀ (a b : ℤ) (x : Fin (b - a + 1).toNat),
      a ≤ (x.1.toInt64 + a.toInt64).toInt ∧ (x.1.toInt64 + a.toInt64).toInt ≤ b := by
  intro h
  have h1 := (h (2^63 - 1) (2^63) ⟨1, by decide⟩).1
  revert h1
  decide

end SciLean.SorryProofObstructions
