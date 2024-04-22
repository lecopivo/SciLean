import Mathlib.Data.RCLike.Basic
import Mathlib.Data.Real.EReal

import SciLean.Core.NotationOverField

namespace SciLean

class IsReal (R : semiOutParam $ Type _) extends RCLike R where
  is_real : ∀ x : R, im x = 0

noncomputable
instance : IsReal ℝ where
  is_real := by simp


inductive ExtendedReal (R : Type _) where
  | val (r : R)
  | posInf
  | negInf

def ExtendedReal.toEReal (R : Type _) [IsReal R] (x : ExtendedReal R) : EReal :=
  match x with
  | .val r => .some (.some (RCLike.re r))
  | .posInf => .some .none
  | .negInf => .none

instance (R : Type _) [IsReal R] : Bot (ExtendedReal R) := ⟨.negInf⟩
instance (R : Type _) [IsReal R] : Top (ExtendedReal R) := ⟨.posInf⟩
instance (R : Type _) [IsReal R] : Zero (ExtendedReal R) := ⟨.val 0⟩
instance (R : Type _) [IsReal R] : One (ExtendedReal R) := ⟨.val 1⟩
instance (R : Type _) [IsReal R] : Neg (ExtendedReal R) := ⟨fun x =>
  match x with
  | .val x' => .val (-x')
  | .posInf => .negInf
  | .negInf => .posInf⟩
-- instance (R : Type _) [IsReal R] : Nontrivial (ExtendedReal R) := ⟨⟩
instance (R : Type _) [IsReal R] [Ord R] : Ord (ExtendedReal R) := ⟨fun x y =>
  match x, y with
  | .val x', .val y' => compare x' y'
  | .val _, .posInf => .lt
  | .val _, .negInf => .gt
  | .posInf, .val _ => .gt
  | .posInf, .posInf => .eq
  | .posInf, .negInf => .gt
  | .negInf, .val _ => .lt
  | .negInf, .posInf => .lt
  | .negInf, .negInf => .eq⟩
-- instance (R : Type _) [IsReal R] : PartialOrder (ExtendedReal R) := by unfold ExtendedReal; infer_instance

-- instance : ZeroLEOneClass EReal := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℝ)))
-- instance : SupSet EReal := inferInstanceAs (SupSet (WithBot (WithTop ℝ)))
-- instance : InfSet EReal := inferInstanceAs (InfSet (WithBot (WithTop ℝ)))

-- instance : CompleteLinearOrder EReal :=
--   inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℝ)))

-- instance : LinearOrderedAddCommMonoid EReal :=
--   inferInstanceAs (LinearOrderedAddCommMonoid (WithBot (WithTop ℝ)))

-- instance : DenselyOrdered EReal :=
--   inferInstanceAs (DenselyOrdered (WithBot (WithTop ℝ)))


class ComputableDist (R : Type _) (X : Type _) [IsReal R] [Dist X] where
  cdist : X → X → R
  is_dist : ∀ x y, RCLike.re (cdist x y) = dist x y

export ComputableDist (cdist)

class ComputableEDist (R : Type _) (X : Type _) [IsReal R] [EDist X] where
  cedist : X → X → ExtendedReal R
  is_edist : ∀ x y, (cedist x y).toEReal = edist x y

export ComputableEDist (cedist)

class ComputableNorm (R : Type _) (X : Type _) [IsReal R] [Norm X] where
  cnorm : X → R
  is_norm : ∀ x, RCLike.re (cnorm x) = norm x

export ComputableNorm (cnorm)

namespace NotationOverField

open Lean Elab Term

/-- Norm, usually `‖x‖ = (∑ i, ‖x i‖^p)^(1/p)` for some `p`

  WARRNING: This is override for normal norm notation that provides computable version of norm if available.
-/
scoped elab (priority := high) "‖" x:term "‖" : term => do
  elabTerm (← `(cnorm (R:=defaultScalar%) $x)) none
  -- TODO: fall back to normal norm if

end NotationOverField
