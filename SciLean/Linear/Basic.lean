import SciLean.Prelude

variable {X : Type u} {Y : Type u} {Z : Type w} [Vec X] [Vec Y] [Vec Z]


instance : IsLin (Prod.fst : X × Y→ X) := sorry
instance : IsLin (Prod.snd : X × Y→ Y) := sorry
