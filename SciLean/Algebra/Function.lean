
def injective {α β} (f : α → β) : Prop := ∀ x x', f x ≠ f x' → x ≠ x'
def surjective {α β} (f : α → β) : Prop := ∀ y, ∃ x, f x = y
def bijective {α β} (f : α → β) : Prop := injective f ∧ surjective f
