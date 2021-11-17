import SciLean.Categories.Zero.Basic

namespace SciLean

-- instance (x : ℝ) [NonZero x] [NonNeg x] : IsPos x := ⟨⟩

instance (x y : ℝ) [NonNeg x] [NonNeg y] : NonNeg (x + y) := sorry
instance (x y : ℝ) [IsPos x] [NonNeg y] : NonZero (x + y) := sorry
instance (x y : ℝ) [NonNeg x] [IsPos y] : NonZero (x + y) := sorry
instance (x y : ℝ) [IsPos x] [IsPos y] : IsPos (x + y) := ⟨⟩

instance [NonZero n] : Inhabited (Fin n) := ⟨⟨0, sorry⟩⟩
