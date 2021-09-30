import SciLean.Prelude

variable {X Y Z : Type} [Vec X] [Vec Y] [Vec Z]

-- Product
instance : IsLin (Prod.fst : X × Y→ X) := sorry
instance : IsLin (Prod.snd : X × Y→ Y) := sorry
-- Pairing with zero is linear
instance (x : X) [IsZero x] : IsLin (Prod.mk x : Y → X × Y) := sorry
instance (y : Y) [IsZero y] : IsLin (swap Prod.mk y : X → X × Y) := sorry

-- Multiplication
instance : IsLin (HMul.hMul : ℝ → X → X) := sorry
instance (s : ℝ) : IsLin (HMul.hMul s : X → X) := sorry
instance (s : ℝ) : IsLin (HMul.hMul s : ℝ → ℝ) := sorry

-- Addition - only adding a zero is linear
instance (x : X) [IsZero x] : IsLin (HAdd.hAdd x : X → X) := sorry 
instance (x : X) [IsZero x] : IsLin (swap HAdd.hAdd x : X → X) := sorry 

-- Constantly zero map is linear
instance (f : X → Y) [IsZero f] : IsLin f := sorry

-----------------------------------------------------------------------------------

variable {U : Type u} {V : Type v} {W : Type w} [Hilbert U] [Hilbert V] [Hilbert W]

instance : IsLin (Inner.inner : U → U → ℝ) := sorry
instance (u : U) : IsLin (Inner.inner u : U → ℝ) := sorry



