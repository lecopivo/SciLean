import Mathlib.Data.Set.Basic

import SciLean.Tactic.FTrans.Simp


/-- Take a slice of a set in the first component. -/
@[pp_dot]
def Set.fst (A : Set (α×β)) (b : β) : Set α := {x | (x,b) ∈ A}

/-- Take a slice of a set in the second component. -/
@[pp_dot]
def Set.snd (A : Set (α×β)) (a : α) : Set β := {y | (a,y) ∈ A}


@[simp, ftrans_simp]
theorem Set.mem_fst (x : α) (b : β) (A : Set (α×β)) : (x ∈ A.fst b) = ((x,b) ∈ A) := by rfl

@[simp, ftrans_simp]
theorem Set.mem_snd (a : α) (y : β) (A : Set (α×β)) : (y ∈ A.snd a) = ((a,y) ∈ A) := by rfl
