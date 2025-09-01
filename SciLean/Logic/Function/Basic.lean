import SciLean.Meta.SimpCore

@[simp,simp_core] theorem Function.HasUncurry.uncurry_apply_1 (f : α → β) (x : α) : (↿f) x = f x := by rfl
@[simp,simp_core] theorem Function.HasUncurry.uncurry_apply_2 (f : α → β → γ) (x : α) (y : β) : (↿f) (x,y) = f x y := by rfl
@[simp,simp_core] theorem Function.HasUncurry.uncurry_apply_3 (f : α → β → γ → δ) (x : α) (y : β) (z : γ) : (↿f) (x,y,z) = f x y z := by rfl
@[simp,simp_core] theorem Function.HasUncurry.uncurry_apply_4 (f : α → β → γ → δ → ε) (x : α) (y : β) (z : γ) (w : δ) : (↿f) (x,y,z,w) = f x y z w := by rfl
@[simp,simp_core] theorem Function.HasUncurry.uncurry_apply_5 (f : α → β → γ → δ → ε → ζ) (x : α) (y : β) (z : γ) (w : δ) (v : ε) : (↿f) (x,y,z,w,v) = f x y z w v := by rfl
