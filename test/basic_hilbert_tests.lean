import SciLean.Basic
import SciLean.Tactic

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} {S} [Vec S.R] [SemiHilbert' X S] [SemiHilbert' Y S] [SemiHilbert' Z S]
variable {U V W : Type} [Hilbert U] [Hilbert V] [Hilbert W]

example : SemiInner.Trait X := by infer_instance
example : IsLin (SemiInner.semiInner' : X → X → _) := by infer_instance done
example : IsLin (λ x y : X => ⟪S|x, y⟫) := by infer_instance done
example : IsLin (SemiInner'.semiInner : X → X → S.R) := by infer_instance done
example : IsLin (λ x y : X => ⟪x, y⟫) := by infer_instance done
example (x : X) : IsLin (λ y : X => ⟪x, y⟫) := by infer_instance done
example {X' : Type} [SemiHilbert' X' SemiInner.RealSig] : IsLin (SemiInner.semiInner' : X' → X' → _) := by infer_instance


example {X Y R D eval} [Vec R] [FinEnumVec X] [SemiInner' Y ⟨R,D,eval⟩] [Vec Y]
  : SemiInner' (X ⊸ Y) ⟨R,D,eval⟩ := by infer_instance
example {X Y R D eval} [Vec R] [FinEnumVec X] [SemiHilbert' Y ⟨R,D,eval⟩] 
  : SemiHilbert' (X ⊸ Y) ⟨R,D,eval⟩ := by infer_instance
example {X Y S} [Vec S.R] [FinEnumVec X] [SemiInner' Y S] [Vec Y] : SemiInner' (X ⊸ Y) S := by infer_instance
example {X} [FinEnumVec X] : SemiInner' (X ⊸ ℝ) SemiInner.RealSig := by infer_instance
example {X Y S} [Vec S.R] [FinEnumVec X] [SemiHilbert' Y S] : SemiHilbert' (X ⊸ Y) S := by infer_instance
example {X} [FinEnumVec X] : Hilbert (X ⊸ ℝ) := by infer_instance

-- example {X} [FinEnumVec X] : SemiInner' (X ⊸ ℝ) (SemiInner.RealSig) := by infer_instance
-- example {X} [FinEnumVec X] : Hilbert (X ⊸ ℝ) := by infer_instance

-- by apply Lin.instIsLinSemiInnerArrowArrow; done

-- #check Lin.instIsLinSemiInnerArrowArrow




-- This was a problem at some point
section mul_test
  variable {X : Type} [Hilbert X] (x y : X) (r s : ℝ)
  #check r * x
end mul_test
