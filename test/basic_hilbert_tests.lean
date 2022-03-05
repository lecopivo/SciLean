import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type}[SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

example : IsLin (SemiInner.semiInner : X → X → _) := by infer_instance done
example : IsLin (λ x y : X => ⟪x, y⟫) := by infer_instance done
example (x : X) : IsLin (λ y : X => ⟪x, y⟫) := by infer_instance done

-- example {X Y R D eval} [Vec R] [FinVec X] [SemiInner Y R D eval] [Vec Y]
--   : SemiInner (X ⊸ Y) R D eval := by infer_instance

-- example {X Y R D eval} [Vec R] [FinVec X] [SemiHilbert Y R D eval] 
--   : SemiHilbert (X ⊸ Y) R D eval := by infer_instance

-- example {X Y R D e} [Vec R] [FinVec X] [SemiInner Y R D e] [Vec Y] : SemiInner (X ⊸ Y) R D e := by infer_instance
-- example {X Y R D e} [Vec R] [FinVec X] [SemiHilbert Y R D e]       : SemiHilbert (X ⊸ Y) R D e := by infer_instance

-- example {X Y} [FinVec X] [Hilbert Y] : Hilbert (X ⊸ Y) := by infer_instance
-- example {Y}                  [Hilbert Y] : Hilbert (ℝ ⊸ Y) := by infer_instance

-- example {X} [FinVec X] : SemiInner (X ⊸ ℝ) ℝ Unit (λ r _ => r) := by infer_instance
-- example {X} [FinVec X] : Hilbert    (X ⊸ ℝ)                     := by infer_instance


-- This was a problem at some point
section mul_test
  variable {X : Type} [Hilbert X] (x y : X) (r s : ℝ)
  #check r * x
end mul_test
