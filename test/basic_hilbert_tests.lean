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
-- by apply Lin.instIsLinSemiInnerArrowArrow; done

-- #check Lin.instIsLinSemiInnerArrowArrow
