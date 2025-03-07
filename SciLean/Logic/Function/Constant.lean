
/-- `IsConstant f` implies that function `f` is a constant function. -/
def Function.IsConstant (f : α → β) : Prop := ∀ x y, f x = f y
