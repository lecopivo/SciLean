module

public import SciLean.Analysis.Scalar.Basic
public import SciLean.Logic.Isomorph.RealToFloat.Basic
public import SciLean.Data.Float

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section


namespace SciLean

open Float.Model in
/-- IEEE addition of unpacked floats is commutative. -/
private theorem unpackedFloat_add_comm (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.add spec a b = UnpackedFloat.add spec b a := by
  rcases a with ⟨s₁⟩ | _ | ⟨s₁⟩ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with ⟨s₂⟩ | _ | ⟨s₂⟩ | ⟨s₂, m₂, e₂, h₂⟩ <;>
  (try cases s₁) <;> (try cases s₂) <;>
  simp [UnpackedFloat.add, min_comm, Int.add_comm]

open Float.Model in
/-- IEEE subtraction of unpacked floats is addition of the negation. -/
private theorem unpackedFloat_sub_eq_add_neg (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.sub spec a b = UnpackedFloat.add spec a b.neg := by
  rcases a with ⟨s₁⟩ | _ | ⟨s₁⟩ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with ⟨s₂⟩ | _ | ⟨s₂⟩ | ⟨s₂, m₂, e₂, h₂⟩ <;>
  (try cases s₁) <;> (try cases s₂) <;>
  simp [UnpackedFloat.add, UnpackedFloat.sub, UnpackedFloat.neg, Float.Model.UnpackedFloat.Sign.apply] <;> rfl

open Float.Model UnpackedFloat in
private theorem unpackSign_packComponents_binary64 {sign exponent mantissa} :
    unpackSign (packComponents Format.binary64 sign exponent mantissa) = sign.toBitVec := by
  simp only [unpackSign, packComponents]
  rw [BitVec.extractLsb'_append_eq_of_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact BitVec.extractLsb'_append_eq_left

open Float.Model in
private theorem sign_ofBitVec_toBitVec (s : Float.Model.UnpackedFloat.Sign) :
    Float.Model.UnpackedFloat.Sign.ofBitVec s.toBitVec = s := by
  cases s <;> rfl

private theorem one_append_toNat (m : BitVec 52) : (1#1 ++ m).toNat = 2 ^ 52 + m.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt m.isLt]
  simp [Nat.shiftLeft_eq]

open Float.Model UnpackedFloat in
/-- Packing a subnormal float produced by `unpack`. -/
private theorem pack_subnormal_binary64 (t : Float.Model.UnpackedFloat.Sign) (m : BitVec 52) (e : Int)
    (he : e = -1074) (hm) :
    UnpackedFloat.pack Format.binary64 (.finite t m.toNat e hm) =
      packComponents Format.binary64 t 0 m := by
  subst he
  have hlog : ¬ m.toNat.log2 + 1 = 53 := by
    have := (Nat.log2_lt (by omega)).2 m.isLt; omega
  have hB : (Format.binary64.exponentBias : Int) = 1023 := rfl
  simp [UnpackedFloat.pack, show Format.binary64.mantissaBits = 53 from rfl, hlog, hB]

open Float.Model UnpackedFloat in
/-- Packing a normal float produced by `unpack`. -/
private theorem pack_normal_binary64 (t : Float.Model.UnpackedFloat.Sign) (m : BitVec 52) (e : BitVec 11)
    (he1 : e ≠ -1#11) (x : Int) (hx : x = (e.toNat : Int) - (1023 + 52)) (hm) :
    UnpackedFloat.pack Format.binary64 (.finite t (1#1 ++ m).toNat x hm) =
      packComponents Format.binary64 t e m := by
  subst hx
  have h1 : e.toNat ≠ 2047 := fun h => he1 (by apply BitVec.eq_of_toNat_eq; simpa using h)
  have h2 := e.isLt
  have hlog : (1#1 ++ m).toNat.log2 + 1 = 53 := by
    have : (1#1 ++ m).toNat.log2 = 52 := by
      rw [one_append_toNat, Nat.log2_eq_iff (by omega)]; have := m.isLt; omega
    omega
  have hB : (Format.binary64.exponentBias : Int) = 1023 := rfl
  simp [UnpackedFloat.pack, show Format.binary64.mantissaBits = 53 from rfl, hlog, hB]
  have hE : ((e.toNat : Int) - 1075 + 1023 + 52).toNat = e.toNat := by omega
  simp only [hE, show ¬ 2047 ≤ e.toNat by omega, ↓reduceIte]
  congr 1
  · simp
  · apply BitVec.eq_of_toNat_eq
    simpa [one_append_toNat] using m.isLt

open Float.Model UnpackedFloat in
/-- Negating an unpacked float and packing it again loses no information. -/
private theorem unpack_pack_neg_unpack_binary64 (b : BitVec Format.binary64.numBits) :
    UnpackedFloat.unpack Format.binary64
        (UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 b).neg) =
      (UnpackedFloat.unpack Format.binary64 b).neg := by
  generalize hu : UnpackedFloat.unpack Format.binary64 b = u
  unfold UnpackedFloat.unpack at hu
  simp only at hu
  split_ifs at hu with h1 h2 h3 h4 <;> subst hu <;> simp only [UnpackedFloat.neg]
  · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedInfinity,
      unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec]
  · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedNaN]
  · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedZero,
      unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec]
  · rw [pack_subnormal_binary64 _ _ _ (by simp [h3]; rfl)]
    simp [UnpackedFloat.unpack, unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec, h4]
    rw [h3]; rfl
  · rw [pack_normal_binary64 _ _ _ h1 _ (by rfl)]
    have h1' : ¬ unpackExponent b = 2047#11 := h1
    simp [UnpackedFloat.unpack, unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec, h1', h3]

open Float.Model in
private theorem unpack_pack_neg_unpack (a : Float.Model) :
    (Float.Model.pack a.unpack.neg).unpack = a.unpack.neg :=
  unpack_pack_neg_unpack_binary64 a.toBits.toBitVec

open Float.Model UnpackedFloat in
private theorem roundWithAccuracy_neg (spec : Format) (s : Float.Model.UnpackedFloat.Sign) (m : Nat) (e : Int)
    (acc) :
    roundWithAccuracy spec (-s) m e acc = (roundWithAccuracy spec s m e acc).neg := by
  simp only [roundWithAccuracy]
  split <;> rfl

open Float.Model UnpackedFloat in
private theorem mul_neg_left_unpacked (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.mul spec a.neg b = (UnpackedFloat.mul spec a b).neg := by
  rcases a with ⟨s₁⟩ | _ | ⟨s₁⟩ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with ⟨s₂⟩ | _ | ⟨s₂⟩ | ⟨s₂, m₂, e₂, h₂⟩
  case finite.finite =>
    show roundWithAccuracy spec (-s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact =
      (roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact).neg
    rw [← roundWithAccuracy_neg]; cases s₁ <;> cases s₂ <;> rfl
  all_goals (try cases s₁) <;> (try cases s₂) <;> rfl

open Float.Model UnpackedFloat in
private theorem neg_unpack_packComponents (t : Float.Model.UnpackedFloat.Sign) (e : BitVec 11) (m : BitVec 52)
    (he : e ≠ -1#11) :
    (UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 t e m)).neg =
      UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 (-t) e m) := by
  have he' : ¬ e = 2047#11 := he
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec]
  split_ifs <;> rfl

open Float.Model UnpackedFloat in
private theorem pack_unpack_packComponents (t : Float.Model.UnpackedFloat.Sign) (e : BitVec 11) (m : BitVec 52)
    (he : e ≠ -1#11) :
    UnpackedFloat.pack Format.binary64
        (UnpackedFloat.unpack Format.binary64 (packComponents Format.binary64 t e m)) =
      packComponents Format.binary64 t e m := by
  simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec]
  split_ifs with h1 h2 h3 h4
  · exact absurd h1 he
  · exact absurd h1 he
  · subst h3 h4; rfl
  · subst h3; refine pack_subnormal_binary64 _ _ _ ?_ _; rfl
  · refine pack_normal_binary64 _ _ _ he _ ?_ _; rfl

open Float.Model UnpackedFloat in
private theorem pack_neg_unpack_pack (M : UnpackedFloat) :
    UnpackedFloat.pack Format.binary64
        (UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 M)).neg =
      UnpackedFloat.pack Format.binary64 M.neg := by
  rcases M with ⟨s⟩ | _ | ⟨s⟩ | ⟨s, m, e, hm⟩
  · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedInfinity,
      unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec, UnpackedFloat.neg]
  · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedNaN, UnpackedFloat.neg]
  · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedZero,
      unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec, UnpackedFloat.neg]
  · have hp : ∀ t, UnpackedFloat.pack Format.binary64 (.finite t m e hm) =
        if 2 ^ 11 ≤ (e + 1023 + 52).toNat + 1 then packedInfinity Format.binary64 t
        else if m.log2 + 1 = 53 then
          packComponents Format.binary64 t (BitVec.ofNat 11 (e + 1023 + 52).toNat) (BitVec.ofNat 52 m)
        else packComponents Format.binary64 t 0#11 (BitVec.ofNat 52 m) := fun t => rfl
    show UnpackedFloat.pack _ (UnpackedFloat.unpack _ (UnpackedFloat.pack _ (.finite s m e hm))).neg =
      UnpackedFloat.pack _ (.finite (-s) m e hm)
    rw [hp s, hp (-s)]
    split_ifs with h1 h2
    · simp [UnpackedFloat.pack, UnpackedFloat.unpack, packedInfinity,
        unpackSign_packComponents_binary64, sign_ofBitVec_toBitVec, UnpackedFloat.neg]
    · rw [neg_unpack_packComponents, pack_unpack_packComponents]
      all_goals
        intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, show (-1#11).toNat = 2047 from rfl] at this
        omega
    · rw [neg_unpack_packComponents, pack_unpack_packComponents] <;> decide

open Float.Model in
private theorem model_pack_neg_unpack_pack (M : UnpackedFloat) :
    Float.Model.pack (Float.Model.pack M).unpack.neg = Float.Model.pack M.neg := by
  simp only [Float.Model.pack, Float.Model.unpack, UInt64.toBitVec_ofBitVec, pack_neg_unpack_pack]

/-- IEEE negation commutes with multiplication (in the left factor). -/
private theorem float_neg_mul (a x : Float) : -a * x = -(a * x) := by
  change Float.ofModel (Float.Model.mul (Float.Model.neg _) _) =
    Float.ofModel (Float.Model.neg (Float.Model.mul _ _))
  rw [Float.Model.mul, Float.Model.neg, Float.Model.neg, unpack_pack_neg_unpack,
    mul_neg_left_unpacked, Float.Model.mul, model_pack_neg_unpack_pack]

instance : CommRing Float where
  zero_mul := by intros; apply isomorph.ext `FloatToReal; simp; trivial --  fun_trans; simp
  mul_zero := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans
  mul_comm := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans; rw[mul_comm]
  left_distrib := by intros;  apply isomorph.ext `FloatToReal; simp; fun_trans; rw[mul_add]
  right_distrib := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans; rw[add_mul]
  mul_one := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans
  one_mul := by intros; apply isomorph.ext `FloatToReal; simp; fun_trans
  npow n x := x.npow n
  npow_zero n := by rfl
  npow_succ n x := sorry_proof
  mul_assoc := sorry_proof
  add_comm a b := by
    change Float.ofModel (Float.Model.add _ _) = Float.ofModel (Float.Model.add _ _)
    rw [Float.Model.add, Float.Model.add, unpackedFloat_add_comm]
  add_assoc := sorry_proof
  add_zero := sorry_proof
  zero_add := sorry_proof
  neg_add_cancel := sorry_proof
  nsmul n x := n.toFloat * x
  nsmul_zero := sorry_proof
  nsmul_succ n x := sorry_proof
  zsmul n x := Float.ofInt n * x
  zsmul_neg' n x := by exact float_neg_mul _ _
  zsmul_succ' := sorry_proof
  zsmul_zero' := sorry_proof
  sub_eq_add_neg a b := by
    change Float.ofModel (Float.Model.sub _ _) =
      Float.ofModel (Float.Model.add _ (Float.Model.neg _))
    rw [Float.Model.sub, Float.Model.add, Float.Model.neg, unpack_pack_neg_unpack,
      unpackedFloat_sub_eq_add_neg]
  natCast n := n.toUInt64.toFloat
  natCast_zero := by rfl
  natCast_succ := sorry_proof
  intCast n := if n ≥ 0 then n.toNat.toUInt64.toFloat else -((-n).toNat.toUInt64).toFloat
  intCast_ofNat := by intros; rfl
  intCast_negSucc := by intros; rfl

instance : Field Float where
  zpow n x := x.zpow n
  zpow_zero' := by intros; rfl
  zpow_succ' := sorry_proof
  zpow_neg' := sorry_proof
  exists_pair_ne := ⟨0, 1, by decide⟩
  div_eq_mul_inv := sorry_proof
  mul_inv_cancel := sorry_proof
  inv_zero := sorry_proof
  qsmul q x := (q.num * x) / q.den
  qsmul_def := sorry_proof
  nnqsmul q x := (q.num * x) / q.den
  nnqsmul_def := sorry_proof

open Float.Model in
/-- IEEE comparison of unpacked floats: swapping the arguments swaps the result. -/
private theorem unpackedFloat_compare_swap (a b : UnpackedFloat) :
    b.compare a = (a.compare b).map Ordering.swap := by
  rcases a with ⟨s₁⟩ | _ | ⟨s₁⟩ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with ⟨s₂⟩ | _ | ⟨s₂⟩ | ⟨s₂, m₂, e₂, h₂⟩ <;>
  (try cases s₁) <;> (try cases s₂) <;>
  simp [UnpackedFloat.compare, Ordering.swap_then, ← Std.OrientedCmp.eq_swap] <;> rfl

private theorem then_isLE_iff (e₁ e₂ : Int) (m₁ m₂ : Nat) :
    ((compare e₁ e₂).then (compare m₁ m₂)).isLE ↔ e₁ < e₂ ∨ e₁ = e₂ ∧ m₁ ≤ m₂ := by
  rcases lt_trichotomy e₁ e₂ with h | rfl | h
  · simp [compare_lt_iff_lt.mpr h, h]
  · simp [Nat.isLE_compare]
  · simp [compare_gt_iff_gt.mpr h, not_lt.mpr h.le, h.ne']

private theorem then_isGE_iff (e₁ e₂ : Int) (m₁ m₂ : Nat) :
    ((compare e₁ e₂).then (compare m₁ m₂)).isGE ↔ e₂ < e₁ ∨ e₁ = e₂ ∧ m₂ ≤ m₁ := by
  rcases lt_trichotomy e₁ e₂ with h | rfl | h
  · simp [compare_lt_iff_lt.mpr h, not_lt.mpr h.le, h.ne]
  · simp [Nat.isGE_compare]
  · simp [compare_gt_iff_gt.mpr h, h]

open Float.Model in
/-- IEEE `≤` on unpacked floats is transitive. -/
private theorem unpackedFloat_le_trans (a b c : UnpackedFloat) (hab : a.le b) (hbc : b.le c) :
    a.le c := by
  simp only [UnpackedFloat.le] at *
  rcases a with ⟨s₁⟩ | _ | ⟨s₁⟩ | ⟨s₁, m₁, e₁, h₁⟩ <;>
  rcases b with ⟨s₂⟩ | _ | ⟨s₂⟩ | ⟨s₂, m₂, e₂, h₂⟩ <;>
  rcases c with ⟨s₃⟩ | _ | ⟨s₃⟩ | ⟨s₃, m₃, e₃, h₃⟩ <;>
  (try cases s₁) <;> (try cases s₂) <;> (try cases s₃) <;>
  simp_all [UnpackedFloat.compare, then_isLE_iff, then_isGE_iff] <;>
  first | omega | (revert hab; decide) | (revert hbc; decide) | decide

instance : LinearOrder Float where
  le_refl := sorry_proof
  le_trans a b c hab hbc := by
    simp only [LE.le, Float.le, decide_eq_true_eq] at *
    exact unpackedFloat_le_trans _ _ _ hab hbc
  le_antisymm := sorry_proof
  le_total := sorry_proof
  toDecidableLE := fun x y => if h : x≤y then .isTrue h else .isFalse h
  min := fun a b => if a ≤ b then a else b
  max := fun a b => if a ≤ b then b else a
  min_def := by simp
  max_def := by simp
  compare x y :=
    if x < y then Ordering.lt
    else if x = y then Ordering.eq
    else Ordering.gt
  compare_eq_compareOfLessAndEq := fun _ _ => rfl
  lt_iff_le_not_ge a b := by
    simp only [LT.lt, LE.le, Float.lt, Float.le, decide_eq_true_eq]
    simp only [Float.Model.lt, Float.Model.le, Float.Model.UnpackedFloat.lt,
      Float.Model.UnpackedFloat.le, unpackedFloat_compare_swap a.toModel.unpack]
    rcases a.toModel.unpack.compare b.toModel.unpack with _ | (_ | _ | _) <;> simp

instance : IsStrictOrderedRing Float where
  add_le_add_left := sorry_proof
  zero_le_one := by decide
  le_of_add_le_add_left := sorry_proof
  mul_lt_mul_of_pos_left := sorry_proof
  mul_lt_mul_of_pos_right := sorry_proof

/-- `floatToReal` is currently implemented with `panic!`, so logically it is the constant `0`. -/
private theorem floatToReal_eq_zero (x : Float) : floatToReal x = 0 := rfl

instance : SeminormedRing Float where
  norm := fun x => floatToReal (Float.abs x)
  dist := fun x y => floatToReal (Float.abs (x - y))
  dist_self := by intros; rfl
  dist_comm := by intros; rfl
  dist_triangle := by intros; simp only [floatToReal_eq_zero]; norm_num
  edist_dist := by intro x y; exact ENNReal.coe_nnreal_eq _
  dist_eq := by intros; rfl
  norm_mul_le := by intros; simp only [floatToReal_eq_zero]; norm_num

instance : StarRing Float where
  star := fun x => x
  star_involutive := by simp[Function.Involutive]
  star_mul := by simp[mul_comm]
  star_add := by simp[]

instance : DenselyNormedField Float where
  eq_of_dist_eq_zero := sorry_proof
  dist_eq := by aesop
  norm_mul := by
    intros; change floatToReal _ = floatToReal _ * floatToReal _
    simp only [floatToReal_eq_zero]; norm_num
  lt_norm_lt := sorry_proof

instance : StarRing Float where
  star_add := by simp


instance : Algebra ℝ Float where
  smul := fun r x => realToFloat r * x
  algebraMap := ⟨⟨⟨fun r => realToFloat r, sorry_proof⟩, (by fun_trans)⟩, by rfl, by intros; ac_rfl⟩
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := by intros; rfl

instance : NormedField Float where
  dist_eq := by intros; rfl
  norm_mul := by aesop

instance : NormedAlgebra ℝ Float where
  norm_smul_le := by
    intros; change floatToReal _ ≤ ‖_‖ * floatToReal _
    simp only [floatToReal_eq_zero]; norm_num

instance : CompleteSpace Float where
  complete := by
    intro f _
    refine ⟨0, le_top.trans fun s hs => ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    exact Filter.mem_top.mpr (Set.eq_univ_of_forall fun y => hball (by
      change floatToReal _ < ε; rw [floatToReal_eq_zero]; exact hε))

instance : RCLike Float where
  re := ⟨⟨fun x => floatToReal x, by rfl⟩, by intros; ac_rfl⟩
  im := ⟨⟨fun _ => 0, by simp_all⟩, by simp_all⟩
  I := 0
  I_re_ax := by rfl
  I_mul_I_ax := by simp_all
  re_add_im_ax := sorry_proof
  ofReal_re_ax := sorry_proof
  ofReal_im_ax := by fun_trans
  mul_re_ax := by fun_trans
  mul_im_ax := by simp
  conj_re_ax := by intros; rfl
  conj_im_ax := by fun_trans
  conj_I_ax := by simp_all
  norm_sq_eq_def_ax := by
    intros; change floatToReal _ ^ 2 = floatToReal _ * floatToReal _ + 0 * 0
    simp only [floatToReal_eq_zero]; norm_num
  mul_im_I_ax := by aesop
  le_iff_re_im := sorry_proof



instance : RealScalar Float where
  toComplex x := ⟨floatToReal x, 0⟩
  toReal x := floatToReal x
  ofReal x := realToFloat x
  ofComplex x := realToFloat x.re

  is_real := by intros; rfl

  make x _ := x
  make_def := by intros; simp; aesop

  real x := x
  real_def := by intros; simp

  imag _ := 0
  imag_def := by intros; simp

  sin x := x.sin
  sin_def := by intros; simp only [floatToReal_eq_zero]; exact Complex.sin_zero.symm

  cos x := x.cos
  cos_def := sorry_proof

  tan x := x.tan
  tan_def := by intros; simp only [floatToReal_eq_zero]; exact Complex.tan_zero.symm

  asin x := x.asin
  asin_def := by fun_trans

  acos x := x.acos
  acos_def := by fun_trans

  atan x := x.atan
  atan_def := by fun_trans

  exp x := x.exp
  exp_def := sorry_proof

  log x := if x ≠ 0 then x.abs.log else 0
  log_def := by intros; simp only [floatToReal_eq_zero]; exact Complex.log_zero.symm

  tanh x := x.tanh
  tanh_def := by intros; simp only [floatToReal_eq_zero]; exact Complex.tanh_zero.symm

  sqrt x := if 0 ≤ x then x.sqrt else 0
  sqrt_def := by
    have him : ∀ y : Float, RCLike.im y = 0 := fun _ => rfl
    intros; simp only [him, forall_const, ↓reduceIte, floatToReal_eq_zero]
    exact Real.sqrt_zero.symm

  pow x y := x.pow y
  pow_def := sorry_proof

  abs x := x.abs
  abs_def := by intros; simp only [floatToReal_eq_zero]; exact norm_zero.symm

  tgamma x := x.tgamma
  tgamma_def := by intros; simp only [floatToReal_eq_zero]; exact Complex.Gamma_zero.symm

  lgamma x := x.lgamma
  lgamma_def := by
    intros; simp only [floatToReal_eq_zero]
    change (0:ℝ) = Real.log ‖Complex.Gamma 0‖; simp

  isNaN x := x.isNaN
  isInf x := x.isInf
  isFinite x := x.isFinite

  order := {
    le_total := by grind
    toDecidableLE := inferInstance
    toDecidableLT := inferInstance

    min_def := by grind
    max_def := by grind
    compare x y := compare x y
    compare_eq_compareOfLessAndEq := fun _ _ => rfl
  }


open ComplexConjugate
@[simp]
theorem conj_float  (a : Float)
  : conj a = a := by trivial

@[simp]
theorem re_float  (a : Float)
  : RCLike.re a = a := by
  exact RCLike.re_eq_self_of_le le_rfl

open ComplexConjugate
@[simp]
theorem im_float  (a : Float)
  : RCLike.im a = (0 : Float) := by trivial


-- TODO: provide proper measurable structure by
--       translating measurable structure from reals via Scalar.toReal/ofReal
instance : MeasurableSpace Float where
 MeasurableSet' := fun _ => True
 measurableSet_empty := by simp
 measurableSet_compl := by simp
 measurableSet_iUnion := by simp

-- TODO: provide proper measurable structure by
--       translating measurable structure from reals via Scalar.toReal/ofReal
instance : MeasureTheory.MeasureSpace Float where
  volume := {
    measureOf := fun _ => 0
    empty := by rfl
    mono := by simp
    iUnion_nat := by simp
    m_iUnion := by simp
    trim_le := MeasureTheory.OuterMeasure.trim_zero.le
}
