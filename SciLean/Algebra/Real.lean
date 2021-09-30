import SciLean.Algebra.Field

def Real := Float
abbrev ℝ := Real

def Float.toReal (x : Float) : Real := x

namespace Real

  def toFloat (x : Real) : Float := x
  instance : ToString Real := ⟨λ x => x.toFloat.toString⟩
  
  instance : LT Real := ⟨λ x y => x.toFloat < y.toFloat⟩
  instance : OfScientific Real := instOfScientificFloat
  
  instance : Add Real := ⟨λ x y => x.toFloat + y.toFloat⟩
  instance : Sub Real := ⟨λ x y => x.toFloat - y.toFloat⟩
  instance : Mul Real := ⟨λ x y => x.toFloat * y.toFloat⟩
  instance : Div Real := ⟨λ x y => x.toFloat / y.toFloat⟩
  instance : Neg Real := ⟨λ x => (-x : Float)⟩
  
  instance : One Real := ⟨(1.0 : Float)⟩
  instance : Zero Real := ⟨(0.0 : Float)⟩

  instance : Field ℝ := sorry

  def sqrt := Float.sqrt

  def sin := Float.sin
  def cos := Float.cos
  def tan := Float.tan
  def atan := Float.atan
  def atan2 := Float.atan2

  def exp := Float.exp
  def exp2 := Float.exp2
  def log := Float.log
  def log2 := Float.log2
  def log10 := Float.log10

end Real

