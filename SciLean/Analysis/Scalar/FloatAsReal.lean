import SciLean.Analysis.Scalar.Basic
import SciLean.Logic.Isomorph.RealToFloat.Basic
import SciLean.Data.Float

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

namespace SciLean

instance : CommRing Float where
  zero_mul := by intros; apply isomorph.ext `FloatToReal; simp; sorry_proof --  fun_trans; simp
  mul_zero := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans
  mul_comm := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans; rw[mul_comm]
  left_distrib := by intros;  apply isomorph.ext `FloatToReal; simp; fun_trans; rw[mul_add]
  right_distrib := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans; rw[add_mul]
  mul_one := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans
  one_mul := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans
  npow n x := x.npow n
  npow_zero n := sorry_proof
  npow_succ n x := sorry_proof
  mul_assoc := sorry_proof
  add_comm := sorry_proof
  add_assoc := sorry_proof
  add_zero := sorry_proof
  zero_add := sorry_proof
  neg_add_cancel := sorry_proof
  nsmul n x := n.toFloat * x
  nsmul_zero := sorry_proof
  nsmul_succ n x := sorry_proof
  zsmul n x := Float.ofInt n * x
  zsmul_neg' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_zero' := sorry_proof
  sub_eq_add_neg a b := sorry_proof
  natCast n := n.toUInt64.toFloat
  natCast_zero := sorry_proof
  natCast_succ := sorry_proof
  intCast n := if n ≥ 0 then n.toNat.toUInt64.toFloat else -((-n).toNat.toUInt64).toFloat
  intCast_ofNat := sorry_proof
  intCast_negSucc := sorry_proof

instance : Field Float where
  zpow n x := x.zpow n
  zpow_zero' := sorry_proof
  zpow_succ' := sorry_proof
  zpow_neg' := sorry_proof
  exists_pair_ne := sorry_proof
  div_eq_mul_inv := sorry_proof
  mul_inv_cancel := sorry_proof
  inv_zero := sorry_proof
  qsmul q x := (q.num * x) / q.den
  qsmul_def := sorry_proof
  nnqsmul q x := (q.num * x) / q.den
  nnqsmul_def := sorry_proof

instance : DecidableEq Float := fun x y =>
  if x ≤ y && y ≤ x
  then .isTrue sorry_proof
  else .isFalse sorry_proof

instance : LinearOrder Float where
  le_refl := sorry_proof
  le_trans := sorry_proof
  le_antisymm := sorry_proof
  le_total := sorry_proof
  toDecidableLE := fun x y => if h : x≤y then .isTrue h else .isFalse h
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  min_def := sorry_proof
  max_def := sorry_proof
  compare x y :=
    if x < y then Ordering.lt
    else if x = y then Ordering.eq
    else Ordering.gt
  compare_eq_compareOfLessAndEq := sorry_proof
  lt_iff_le_not_le := sorry_proof

instance : IsStrictOrderedRing Float where
  add_le_add_left := sorry_proof
  zero_le_one := sorry_proof
  le_of_add_le_add_left := sorry_proof
  mul_lt_mul_of_pos_left := sorry_proof
  mul_lt_mul_of_pos_right := sorry_proof

instance : SeminormedRing Float where
  norm := fun x => floatToReal (Float.abs x)
  dist := fun x y => floatToReal (Float.abs (x - y))
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist_dist := sorry_proof
  dist_eq := sorry_proof
  norm_mul_le := sorry_proof

instance : StarRing Float where
  star := fun x => x
  star_involutive := by simp[Function.Involutive]
  star_mul := by simp[Function.Involutive, mul_comm]
  star_add := by simp[Function.Involutive]

instance : DenselyNormedField Float where
  eq_of_dist_eq_zero := sorry_proof
  dist_eq := sorry_proof
  norm_mul := sorry_proof
  lt_norm_lt := sorry_proof

instance : StarRing Float where
  star_add := sorry_proof


instance : Algebra ℝ Float where
  smul := fun r x => realToFloat r * x
  algebraMap := ⟨⟨⟨fun r => realToFloat r, sorry_proof⟩, sorry_proof⟩, sorry_proof, sorry_proof⟩
  commutes' := sorry_proof
  smul_def' := sorry_proof

instance : NormedField Float where
  dist_eq := sorry_proof
  norm_mul := sorry_proof

instance : NormedAlgebra ℝ Float where
  norm_smul_le := sorry_proof

instance : CompleteSpace Float where
  complete := sorry_proof

instance : RCLike Float where
  re := ⟨⟨fun x => floatToReal x, sorry_proof⟩, sorry_proof⟩
  im := ⟨⟨fun _ => 0, sorry_proof⟩, sorry_proof⟩
  I := 0
  I_re_ax := sorry_proof
  I_mul_I_ax := sorry_proof
  re_add_im_ax := sorry_proof
  ofReal_re_ax := sorry_proof
  ofReal_im_ax := sorry_proof
  mul_re_ax := sorry_proof
  mul_im_ax := sorry_proof
  conj_re_ax := sorry_proof
  conj_im_ax := sorry_proof
  conj_I_ax := sorry_proof
  norm_sq_eq_def_ax := sorry_proof
  mul_im_I_ax := sorry_proof
  le_iff_re_im := sorry_proof



instance : RealScalar Float where
  toComplex x := ⟨floatToReal x, 0⟩
  toReal x := floatToReal x
  ofReal x := realToFloat x
  ofComplex x := realToFloat x.re

  is_real := sorry_proof

  make x _ := x
  make_def := by intros; simp; sorry_proof

  real x := x
  real_def := by intros; simp

  imag _ := 0
  imag_def := by intros; simp

  sin x := x.sin
  sin_def := sorry_proof

  cos x := x.cos
  cos_def := sorry_proof

  tan x := x.tan
  tan_def := sorry_proof

  asin x := x.asin
  asin_def := sorry_proof

  acos x := x.acos
  acos_def := sorry_proof

  atan x := x.atan
  atan_def := sorry_proof

  exp x := x.exp
  exp_def := sorry_proof

  log x := if x ≠ 0 then x.abs.log else 0
  log_def := sorry_proof

  tanh x := x.tanh
  tanh_def := sorry_proof

  sqrt x := if 0 ≤ x then x.sqrt else 0
  sqrt_def := sorry_proof

  pow x y := x.pow y
  pow_def := sorry_proof

  abs x := x.abs
  abs_def := sorry_proof

  tgamma x := x.tgamma
  tgamma_def := sorry_proof

  lgamma x := x.lgamma
  lgamma_def := sorry_proof

  isNaN x := x.isNaN
  isInf x := x.isInf
  isFinite x := x.isFinite

  order := {
    le_total := by sorry_proof
    toDecidableLE := inferInstance
    toDecidableLT := inferInstance
    toDecidableEq := inferInstance

    min_def := by sorry_proof
    max_def := by sorry_proof
    compare x y := compare x y
    compare_eq_compareOfLessAndEq := by sorry_proof
  }


open ComplexConjugate
@[simp]
theorem conj_float  (a : Float)
  : conj a = a := sorry_proof

@[simp]
theorem re_float  (a : Float)
  : RCLike.re a = a := by sorry_proof

open ComplexConjugate
@[simp]
theorem im_float  (a : Float)
  : RCLike.im a = (0 : Float) := sorry_proof


-- TODO: provide proper measurable structure by
--       translating measurable structure from reals via Scalar.toReal/ofReal
instance : MeasurableSpace Float where
 MeasurableSet' := fun _ => True
 measurableSet_empty := sorry_proof
 measurableSet_compl := sorry_proof
 measurableSet_iUnion := sorry_proof

-- TODO: provide proper measurable structure by
--       translating measurable structure from reals via Scalar.toReal/ofReal
instance : MeasureTheory.MeasureSpace Float where
  volume := {
    measureOf := fun _ => 0
    empty := sorry_proof
    mono := sorry_proof
    iUnion_nat := sorry_proof
    m_iUnion := sorry_proof
    trim_le := sorry_proof
}
