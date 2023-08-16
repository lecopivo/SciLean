import SciLean.Core.FunctionTransformations.Isomorph.RealToFloat
import SciLean.Core.Objects.IsReal

namespace SciLean

instance : CommRing Float where
  zero_mul := by intros; apply isomorph.ext `FloatToReal; simp; ftrans
  mul_zero := by intros; apply isomorph.ext `FloatToReal; simp; ftrans
  mul_comm := by intros; apply isomorph.ext `FloatToReal; simp; ftrans; rw[mul_comm]
  left_distrib := by intros;  apply isomorph.ext `FloatToReal; simp; ftrans; ftrans; rw[mul_add]
  right_distrib := by intros; apply isomorph.ext `FloatToReal; simp; ftrans; ftrans; rw[add_mul]
  mul_one := by intros; apply isomorph.ext `FloatToReal; simp; ftrans
  one_mul := by intros; apply isomorph.ext `FloatToReal; simp; ftrans
  npow n x := x.pow (n.toFloat)  --- TODO: change this implementation
  npow_zero n := sorry_proof
  npow_succ n x := sorry_proof
  mul_assoc := sorry_proof
  add_comm := sorry_proof
  add_assoc := sorry_proof
  add_zero := sorry_proof
  zero_add := sorry_proof
  add_left_neg := sorry_proof
  nsmul n x := n.toFloat * x
  nsmul_zero := sorry_proof
  nsmul_succ n x := sorry_proof
  sub_eq_add_neg a b := sorry_proof
  natCast n := n.toFloat
  natCast_zero := sorry_proof
  natCast_succ := sorry_proof
  intCast n := if n ≥ 0 then n.toNat.toFloat else -((-n).toNat).toFloat
  intCast_ofNat := sorry_proof
  intCast_negSucc := sorry_proof

instance : Field Float where
  exists_pair_ne := sorry_proof
  div_eq_mul_inv := sorry_proof 
  mul_inv_cancel := sorry_proof
  inv_zero := sorry_proof

-- instance : LinearOrderedRing Float where
--   le_refl := sorry_proof
--   le_trans := sorry_proof
--   le_antisymm := sorry_proof
--   add_le_add_left := sorry_proof
--   zero_le_one := sorry_proof
--   mul_pos := sorry_proof
--   le_total := sorry_proof
--   decidableLE := fun x y => if h : x ≤ y then isTrue h else isFalse h

-- instance : LinearOrderedField Float := LinearOrderedField.mk

noncomputable
instance : SeminormedRing Float where
  norm := fun x => floatToReal (Float.abs x)
  dist := fun x y => floatToReal (Float.abs (x - y))
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist_dist := sorry_proof
  dist_eq := sorry_proof
  norm_mul := sorry_proof

instance : StarRing Float where
  star := fun x => x
  star_involutive := by simp[Function.Involutive] 
  star_mul := by simp[Function.Involutive, mul_comm] 
  star_add := by simp[Function.Involutive]

noncomputable
instance : IsROrC Float where
  eq_of_dist_eq_zero := sorry_proof
  dist_eq := sorry_proof
  norm_mul' := sorry_proof
  lt_norm_lt := sorry_proof
  smul := fun r x => realToFloat r * x
  toFun := realToFloat
  map_one' := sorry_proof
  map_mul' := sorry_proof
  map_zero' := sorry_proof
  map_add' := sorry_proof
  commutes' := sorry_proof
  smul_def' := sorry_proof
  norm_smul_le := sorry_proof
  complete := sorry_proof
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

noncomputable
instance : IsReal Float where
  is_real := sorry_proof
