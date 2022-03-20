import SciLean.Mathlib.Algebra.Field.Basic

-- def ℝ := Float
-- abbrev ℝ := ℝ
structure ℝ where
  val : Float

def Float.toReal (x : Float) : ℝ := ⟨x⟩

namespace Math

  abbrev toRealFun (f : Float → Float) : ℝ → ℝ 
    := λ x => ⟨f x.val⟩

  abbrev toRealFun₂ (f : Float → Float → Float) : ℝ → ℝ → ℝ 
    := λ x y => ⟨f x.val y.val⟩

  def sqrt : ℝ → ℝ := toRealFun Float.sqrt
  def pow : ℝ → ℝ → ℝ := toRealFun₂ Float.pow

  def sin : ℝ → ℝ := toRealFun Float.sin
  def cos : ℝ → ℝ := toRealFun Float.cos
  def tan : ℝ → ℝ := toRealFun Float.tan
  def atan : ℝ → ℝ := toRealFun Float.atan
  def atan2 : ℝ → ℝ → ℝ := toRealFun₂ Float.atan2

  def exp : ℝ → ℝ := toRealFun Float.exp
  def exp2 : ℝ → ℝ := toRealFun Float.exp2
  def log : ℝ → ℝ := toRealFun Float.log
  def log2 : ℝ → ℝ := toRealFun Float.log2
  def log10 : ℝ → ℝ := toRealFun Float.log10

end Math

namespace ℝ

  def toFloat (x : ℝ) : Float := x.val
  instance : ToString ℝ := ⟨λ x => x.toFloat.toString⟩
  
  instance : LT ℝ := ⟨λ x y => x.toFloat < y.toFloat⟩
  instance : LE ℝ := ⟨λ x y => x.toFloat ≤ y.toFloat⟩
  -- This should override 2.0 interperting as a Float
  -- @[defaultInstance mid+1]
  instance (priority := high) : OfScientific ℝ := ⟨λ m e d => ⟨instOfScientificFloat.1 m e d⟩⟩

  instance (x y : ℝ) : Decidable (x < y) :=                         
    if x.val < y.val
    then isTrue sorry
    else isFalse sorry

  -- this kind of breaks with NaNs but I want to make sure that we never get them as division by zero is zero
  instance (x y : ℝ) : Decidable (x = y) := if (x < y) ∨ (y < x) then isFalse (sorry : x≠y) else isTrue (sorry : x=y)
  
  -- @[irreducible]
  instance : Add ℝ := ⟨λ x y => ⟨x.val + y.val⟩⟩
  -- @[irreducible]
  instance : Sub ℝ := ⟨λ x y => ⟨x.val - y.val⟩⟩
  -- @[irreducible]
  instance : Mul ℝ := ⟨λ x y => ⟨x.val * y.val⟩⟩
  -- @[irreducible]
  instance : Div ℝ := ⟨λ x y => if y = 0.0 then 0.0 else ⟨x.val / y.val⟩⟩
  -- @[irreducible]
  instance : Neg ℝ := ⟨λ x => ⟨-x.val⟩⟩

  -- instance : Zero ℝ := ⟨Float.ofNat 0⟩  
  -- instance : One ℝ  := ⟨Float.ofNat 1⟩
  -- instance : OfNat ℝ n := ⟨Float.ofNat n⟩
  -- instance : OfScientific ℝ := ⟨instOfScientificFloat.1⟩

  -- def natPow (r : ℝ) : Nat → ℝ
  -- | 0 => 1
  -- | n+1 => r * natPow r n

  -- instance : Pow ℝ Nat := ⟨natPow⟩
  instance : HPow ℝ ℝ ℝ := ⟨Math.pow⟩

  -- instance : Numeric ℝ := ⟨λ n => n.toFloat⟩
  instance (n : Nat) : OfNat ℝ n := ⟨⟨n.toFloat⟩⟩
  instance : Coe ℕ ℝ := ⟨λ n => n.toFloat.toReal⟩
  instance : Coe ℤ ℝ := ⟨λ n => (Float.ofInt n).toReal⟩

  instance : Inv ℝ := ⟨λ x => 1/x⟩

  -- instance : HPow ℝ ℤ ℝ := ⟨λ x n => x^(n : ℝ)⟩
  -- ⟨λ x n => 
  --   match n with
  --   | Int.ofNat   k => x^(k : ℝ)
  --   | Int.negSucc k => x^(-(k+1) : ℝ)⟩

--   instance (n : Nat) : OfNat ℝ n := ⟨n.toFloat⟩

-- class Numeric (α : Type u) where
--   ofNat : Nat → α


--   instance : Ring ℝ := 
-- {
-- }

  -- instance : AddSemigroup ℝ :=
  -- {
  --   add_assoc := sorry
  -- }

  -- instance : AddCommSemigroup ℝ :=
  -- {
  --   add_comm := sorry
  -- }

  -- instance : Semigroup ℝ :=
  -- {
  --   mul_assoc := sorry
  -- }

  -- instance : Semiring ℝ := 
  -- {
  --   add_zero := sorry
  --   zero_add := sorry
  --   nsmul_zero' := sorry
  --   nsmul_succ' := sorry
  --   zero_mul := sorry
  --   mul_zero := sorry
  --   one_mul := sorry
  --   mul_one := sorry
  --   npow_zero' := sorry
  --   npow_succ' := sorry

  --   add_comm := sorry
  --   left_distrib := sorry
  --   right_distrib := sorry

  --   mul_assoc := sorry

  --   -- mul_add := sorry
  --   -- add_mul := sorry
  --   -- ofNat_succ := sorry
  -- }

  -- instance : Ring ℝ :=
  -- {
  --   sub_eq_add_neg := sorry
  --   gsmul_zero' := sorry
  --   gsmul_succ' := sorry
  --   gsmul_neg' := sorry
  --   add_left_neg := sorry
  -- }

  instance : CommRing ℝ where
    zero_mul := sorry
    mul_zero := sorry
    mul_comm := sorry
    left_distrib := sorry
    right_distrib := sorry
    mul_one := sorry
    one_mul := sorry
    npow n x := x^(n : ℝ) ----------- !!!
    npow_zero' n := sorry
    npow_succ' n x := sorry
    mul_assoc := sorry
    add_comm := sorry
    add_assoc := sorry
    add_zero := sorry
    zero_add := sorry
    add_left_neg := sorry
    nsmul n x := (n : ℝ) * x ----------------  !!!
    nsmul_zero' := sorry
    nsmul_succ' n x := sorry
    sub_eq_add_neg a b := sorry
    gsmul n x := (n : ℝ) * x --------- !!!
    gsmul_zero' := sorry
    gsmul_succ' n x := sorry
    gsmul_neg' n x := sorry

  -- {
  --   mul_comm := sorry
  -- }

  -- instance : Nontrivial ℝ :=
  -- {
  --   exists_pair_ne := sorry
  -- }

  instance : Field ℝ where
    exists_pair_ne := sorry
    div_eq_mul_inv := sorry 
    mul_inv_cancel := sorry
    inv_zero := sorry
    fpow n x := x^(n : ℝ)   ---------  !!!
    fpow_succ := sorry
    fpow_neg := sorry

  --   -- by admit
  --   mul_assoc := sorry
  --   add_zero := sorry
  --   zero_add := sorry
  --   add_assoc := sorry
  --   add_comm := sorry
  --   nsmul_zero' := sorry
  --   nsmul_succ' := sorry
  --   zero_mul := sorry
  --   mul_zero := sorry
  --   one_mul := sorry
  --   mul_one := sorry
  --   npow_zero' := sorry
  --   npow_succ' := sorry
  --   mul_add := sorry
  --   add_mul := sorry
  --   ofNat_succ := sorry
  --   sub_eq_add_neg := sorry
  --   gsmul_zero' := sorry
  --   gsmul_succ' := sorry
  --   gsmul_neg' := sorry
  --   add_left_neg := sorry
  --   mul_comm := sorry
  --   exists_pair_ne := sorry
  --   div_eq_mul_inv := sorry
  --   mul_inv_cancel := sorry
  --   inv_zero := sorry
  --   hpow_succ := sorry
  --   hpow_neg := sorry
  -- }

end ℝ



