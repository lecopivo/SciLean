import SciLean.Basic
import SciLean.Simp
import SciLean.Tactic

open Function

open SciLean


variable {α β γ : Type}
variable {X Y Z : Type} {R D e} [Vec R] [SemiHilbert X R D e] [SemiHilbert Y R D e] [SemiHilbert Z R D e]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

example : HasAdjoint λ xx : X × X => xx.1 + xx.2 := by infer_instance
example : HasAdjoint λ uu : U × U => uu.1 + uu.2 := by infer_instance
