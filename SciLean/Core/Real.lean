
import SciLean.Prelude
import Mathlib.Algebra.Field.Basic

-- import SciLean.Mathlib.Algebra.Field.Basic

structure Real where
  val : Float

notation " ℝ " => Real

def Float.toReal (x : Float) : ℝ := ⟨x⟩
def Nat.toReal (n : Nat) : ℝ := n.toFloat.toReal
def Int.toReal (n : Int) : ℝ := (Float.ofInt n).toReal

namespace Real

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

  def ceil : ℝ → ℝ := toRealFun Float.ceil
  def floor : ℝ → ℝ := toRealFun Float.floor
  def round : ℝ → ℝ := toRealFun Float.round
  def abs : ℝ → ℝ := toRealFun Float.abs

  def pi : ℝ := ⟨3.14159265359⟩


  def toFloat (x : ℝ) : Float := x.val
  instance : ToString ℝ := ⟨λ x => x.toFloat.toString⟩

  open Lean in
  instance : ToJson ℝ where
    toJson x := toJson x.1

  open Lean in
  instance : FromJson ℝ where
    fromJson? json :=
      match fromJson? (α := Float) json with
      | .error msg => .error msg
      | .ok x => .ok ⟨x⟩

  
  instance : LT ℝ := ⟨λ x y => x.toFloat < y.toFloat⟩
  instance : LE ℝ := ⟨λ x y => x.toFloat ≤ y.toFloat⟩
  -- This should override 2.0 interperting as a Float
  -- @[defaultInstance mid+1]
  instance (priority := high) : OfScientific ℝ := ⟨λ m e d => ⟨instOfScientificFloat.1 m e d⟩⟩

  instance (x y : ℝ) : Decidable (x < y) :=                         
    if x.val < y.val
    then isTrue sorry_proof
    else isFalse sorry_proof

  instance (x y : ℝ) : Decidable (x ≤ y) :=                         
    if x.val ≤ y.val
    then isTrue sorry_proof
    else isFalse sorry_proof

  -- this kind of breaks with NaNs but I want to make sure that we never get them as division by zero is zero
  instance (x y : ℝ) : Decidable (x = y) := if (x < y) ∨ (y < x) then isFalse (sorry_proof : x≠y) else isTrue (sorry_proof : x=y)
  
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

  instance : Zero ℝ := ⟨0.0⟩  
  instance : One ℝ  := ⟨1.0⟩
  -- instance : OfNat ℝ n := ⟨Float.ofNat n⟩
  -- instance : OfScientific ℝ := ⟨instOfScientificFloat.1⟩

  def natPow (r : ℝ) (n : Nat) : ℝ := Id.run do
    let mut s   := if n &&& 1 = 1 then r else 1
    let mut r2i := r
    for i in [1:n.log2+1] do
      r2i  := r2i * r2i
      if (n >>> i) &&& 1 = 1 then
        s := s * r2i
    s

  instance : HPow ℝ Nat ℝ := ⟨natPow⟩
  instance : HPow ℝ ℝ ℝ := ⟨Real.pow⟩

  -- instance : Numeric ℝ := ⟨λ n => n.toFloat⟩
  -- instance (n : Nat) : OfNat ℝ n := ⟨⟨n.toFloat⟩⟩
  -- instance : Coe ℕ ℝ := ⟨λ n => n.toFloat.toReal⟩
  -- instance : Coe ℤ ℝ := ⟨λ n => (Float.ofInt n).toReal⟩


  instance : Inv ℝ := ⟨λ x => 1.0/x⟩

  instance : Coe USize ℝ := ⟨λ n => n.toNat.toReal⟩

  -- Used for Kroneckers delta as  `δᵢⱼ = [[i = j]]`
  notation "[[" p "]]" => if p then (1:ℝ) else (0:ℝ)

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
  --   add_assoc := sorry_proof
  -- }

  -- instance : AddCommSemigroup ℝ :=
  -- {
  --   add_comm := sorry_proof
  -- }

  -- instance : Semigroup ℝ :=
  -- {
  --   mul_assoc := sorry_proof
  -- }

  -- instance : Semiring ℝ where
  --   add_zero := sorry_proof
  --   zero_add := sorry_proof
  --   -- nsmul_zero' := sorry_proof
  --   -- nsmul_succ' := sorry_proof
  --   zero_mul := sorry_proof
  --   mul_zero := sorry_proof
  --   one_mul := sorry_proof
  --   mul_one := sorry_proof
  --   -- npow_zero' := sorry_proof
  --   -- npow_succ' := sorry_proof

  --   add_comm := sorry_proof
  --   left_distrib := sorry_proof
  --   right_distrib := sorry_proof

  --   mul_assoc := sorry_proof

  --   -- mul_add := sorry_proof
  --   -- add_mul := sorry_proof
  --   -- ofNat_succ := sorry_proof

  -- instance : Ring ℝ where
  --   sub_eq_add_neg := sorry_proof
  --   -- gsmul_zero' := sorry_proof
  --   -- gsmul_succ' := sorry_proof
  --   -- gsmul_neg' := sorry_proof
  --   add_left_neg := sorry_proof


  instance : CommRing ℝ where
    zero_mul := sorry_proof
    mul_zero := sorry_proof
    mul_comm := sorry_proof
    left_distrib := sorry_proof
    right_distrib := sorry_proof
    mul_one := sorry_proof
    one_mul := sorry_proof
    -- npow n x := x.natPow n
    -- npow_zero' n := sorry_proof
    -- npow_succ' n x := sorry_proof
    mul_assoc := sorry_proof
    add_comm := sorry_proof
    add_assoc := sorry_proof
    add_zero := sorry_proof
    zero_add := sorry_proof
    add_left_neg := sorry_proof
    -- nsmul n x := (n.toReal) * x ----------------  !!!
    -- nsmul_zero' := sorry_proof
    -- nsmul_succ' n x := sorry_proof
    sub_eq_add_neg a b := sorry_proof
    -- gsmul n x := (n.toReal) * x --------- !!!
    -- gsmul_zero' := sorry_proof
    -- gsmul_succ' n x := sorry_proof
    -- gsmul_neg' n x := sorry_proof
    natCast n := n.toReal
    natCast_zero := sorry_proof
    natCast_succ := sorry_proof
    intCast n := n.toReal
    intCast_ofNat := sorry_proof
    intCast_negSucc := sorry_proof


  -- {
  --   mul_comm := sorry_proof
  -- }

  -- instance : Nontrivial ℝ :=
  -- {
  --   exists_pair_ne := sorry_proof
  -- }


  instance : Field ℝ where
    exists_pair_ne := sorry_proof
    div_eq_mul_inv := sorry_proof 
    mul_inv_cancel := sorry_proof
    inv_zero := sorry_proof
    -- fpow n x := x^(n : ℝ)   ---------  !!!
    -- fpow_succ := sorry_proof
    -- fpow_neg := sorry_proof

  --   -- by admit
  --   mul_assoc := sorry_proof
  --   add_zero := sorry_proof
  --   zero_add := sorry_proof
  --   add_assoc := sorry_proof
  --   add_comm := sorry_proof
  --   nsmul_zero' := sorry_proof
  --   nsmul_succ' := sorry_proof
  --   zero_mul := sorry_proof
  --   mul_zero := sorry_proof
  --   one_mul := sorry_proof
  --   mul_one := sorry_proof
  --   npow_zero' := sorry_proof
  --   npow_succ' := sorry_proof
  --   mul_add := sorry_proof
  --   add_mul := sorry_proof
  --   ofNat_succ := sorry_proof
  --   sub_eq_add_neg := sorry_proof
  --   gsmul_zero' := sorry_proof
  --   gsmul_succ' := sorry_proof
  --   gsmul_neg' := sorry_proof
  --   add_left_neg := sorry_proof
  --   mul_comm := sorry_proof
  --   exists_pair_ne := sorry_proof
  --   div_eq_mul_inv := sorry_proof
  --   mul_inv_cancel := sorry_proof
  --   inv_zero := sorry_proof
  --   hpow_succ := sorry_proof
  --   hpow_neg := sorry_proof
  -- }



end Real



