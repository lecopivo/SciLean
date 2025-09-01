import SciLean.Geometry.Shape.Basic


namespace SciLean

variable
  -- {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]


def segment (a b : X) : Set X := {x | ∃ w : ℝ, x = a + w•(b-a) ∧ 0 ≤ w ∧ w ≤ 1}


instance (t : X) : Translate t ↿segment where
  transform := fun (a,b) => (a+t,b+t)
  is_transform := by
    intros; simp [segment,Function.HasUncurry.uncurry]
    constructor <;>
     (intro ⟨w,_⟩
      apply Exists.intro w _
      sorry_proof)


instance : Reflect ↿(segment (X:=X)) where
  transform := fun (a,b) => (-a,-b)
  is_transform := by
    intros; simp [segment,Function.HasUncurry.uncurry]
    constructor <;>
     (intro ⟨w,_⟩
      apply Exists.intro w _
      sorry_proof)
