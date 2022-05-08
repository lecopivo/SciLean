import SciLean.Mathlib.Algebra.Field.Basic

-- def ℝ := Float
-- abbrev ℝ := ℝ
structure ℝ where
  val : Float

def Float.toReal (x : Float) : ℝ := ⟨x⟩
def Nat.toReal (n : Nat) : ℝ := n.toFloat.toReal
def Int.toReal (n : Int) : ℝ := (Float.ofInt n).toReal

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

  instance : Zero ℝ := ⟨0.0⟩  
  instance : One ℝ  := ⟨1.0⟩
  instance : HPow ℝ ℝ ℝ := ⟨Math.pow⟩
  instance : Inv ℝ := ⟨λ x => 1.0/x⟩

  instance : Coe USize ℝ := ⟨λ n => n.toNat.toReal⟩

  instance : CommRing ℝ where
    zero_mul := sorry
    mul_zero := sorry
    mul_comm := sorry
    left_distrib := sorry
    right_distrib := sorry
    mul_one := sorry
    one_mul := sorry
    npow n x := x^(n.toReal) ----------- !!!
    npow_zero' n := sorry
    npow_succ' n x := sorry
    mul_assoc := sorry
    add_comm := sorry
    add_assoc := sorry
    add_zero := sorry
    zero_add := sorry
    add_left_neg := sorry
    nsmul n x := (n.toReal) * x ----------------  !!!
    nsmul_zero' := sorry
    nsmul_succ' n x := sorry
    sub_eq_add_neg a b := sorry
    gsmul n x := (n.toReal) * x --------- !!!
    gsmul_zero' := sorry
    gsmul_succ' n x := sorry
    gsmul_neg' n x := sorry
    natCast n := n.toReal
    natCast_zero := sorry
    natCast_succ := sorry
    intCast n := n.toReal
    intCast_ofNat := sorry
    intCast_negSucc := sorry


  instance : Field ℝ where
    exists_pair_ne := sorry
    div_eq_mul_inv := sorry 
    mul_inv_cancel := sorry
    inv_zero := sorry
    fpow n x := x^(n : ℝ)   ---------  !!!
    fpow_succ := sorry
    fpow_neg := sorry

end ℝ



