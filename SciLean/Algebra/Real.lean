import SciLean.Algebra.Field

def Real := Float
abbrev ℝ := Real

namespace Field

end Field

def Float.toReal (x : Float) : Real := x

namespace Real

def toFloat (x : Real) : Float := x
instance : ToString Real := ⟨λ x => x.toFloat.toString⟩

instance : Add Real := ⟨λ x y => x.toFloat + y.toFloat⟩
instance : Sub Real := ⟨λ x y => x.toFloat - y.toFloat⟩
instance : Mul Real := ⟨λ x y => x.toFloat * y.toFloat⟩
instance : Div Real := ⟨λ x y => x.toFloat / y.toFloat⟩
instance : Neg Real := ⟨λ x => (-x : Float)⟩
instance : Inv Real := ⟨λ x => (1/x.toFloat : Float)⟩

instance : One Real := ⟨(1.0 : Float)⟩
instance : Zero Real := ⟨(0.0 : Float)⟩

instance : Field ℝ := sorry

end Real

@[simp] def reals_mul_by_one (x : ℝ) : 1 * x = x := sorry
