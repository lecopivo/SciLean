import SciLean.Algebra.Field

def Real := Float
abbrev ℝ := Real

def Float.toReal (x : Float) : Real := x

namespace Math

  def sqrt : ℝ → ℝ := Float.sqrt
  def pow : ℝ → ℝ → ℝ := Float.pow

  def sin : ℝ → ℝ := Float.sin
  def cos : ℝ → ℝ := Float.cos
  def tan : ℝ → ℝ := Float.tan
  def atan : ℝ → ℝ := Float.atan
  def atan2 : ℝ → ℝ → ℝ := Float.atan2

  def exp : ℝ → ℝ := Float.exp
  def exp2 : ℝ → ℝ := Float.exp2
  def log : ℝ → ℝ := Float.log
  def log2 : ℝ → ℝ := Float.log2
  def log10 : ℝ → ℝ := Float.log10

end Math

namespace Real

  def toFloat (x : Real) : Float := x
  instance : ToString Real := ⟨λ x => x.toFloat.toString⟩
  
  instance : LT Real := ⟨λ x y => x.toFloat < y.toFloat⟩
  instance : LE Real := ⟨λ x y => x.toFloat ≤ y.toFloat⟩
  instance : OfScientific Real := instOfScientificFloat
  
  instance : Add Real := ⟨λ x y => x.toFloat + y.toFloat⟩
  instance : Sub Real := ⟨λ x y => x.toFloat - y.toFloat⟩
  instance : Mul Real := ⟨λ x y => x.toFloat * y.toFloat⟩
  instance : Div Real := ⟨λ x y => x.toFloat / y.toFloat⟩
  instance : Neg Real := ⟨λ x => (-x : Float)⟩

  instance : Zero Real := ⟨Float.ofNat 0⟩  
  instance : One Real  := ⟨Float.ofNat 1⟩
  instance : OfNat ℝ n := ⟨Float.ofNat n⟩
  instance : OfScientific ℝ := ⟨instOfScientificFloat.1⟩

  instance : HPow Real Real Real := ⟨Math.pow⟩

  instance : Field ℝ := 
  {
    add_assoc := sorry
    add_comm := sorry
    add_zero := sorry
    zero_add := sorry
    mul_assoc := sorry
    mul_comm := sorry
    mul_one := sorry
    one_mul := sorry
  }

end Real



