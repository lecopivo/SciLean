module

public import SciLean.Geometry.Shape.Basic

@[expose] public section



namespace SciLean

variable
  -- {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]


def segment (a b : X) : Set X := {x | ∃ w : ℝ, x = a + w•(b-a) ∧ 0 ≤ w ∧ w ≤ 1}


instance (t : X) : Translate t ↿segment where
  transform := fun (a,b) => (a+t,b+t)
  is_transform := by
    intro (a,b) x
    simp only [segment, Function.HasUncurry.uncurry, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w,hw,h0,h1⟩
      exact ⟨w, by rw [hw]; module, h0, h1⟩
    · rintro ⟨w,hw,h0,h1⟩
      refine ⟨w, add_right_cancel (b := t) ?_, h0, h1⟩
      rw [hw]; module


instance : Reflect ↿(segment (X:=X)) where
  transform := fun (a,b) => (-a,-b)
  is_transform := by
    intro (a,b) x
    simp only [segment, Function.HasUncurry.uncurry, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w,hw,h0,h1⟩
      exact ⟨w, by rw [hw]; module, h0, h1⟩
    · rintro ⟨w,hw,h0,h1⟩
      refine ⟨w, neg_injective ?_, h0, h1⟩
      rw [hw]; module
