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

-- @[ftrans_simp]
-- theorem _root_.Set.mem_prod_eq' {s : Set α} {t : Set β} :
--     (p ∈ s ×ˢ t) = let p := p; (p.1 ∈ s ∧ p.2 ∈ t) := rfl

-- @[ftrans_simp]
-- theorem _root_.Set.mem_Ioo' {α} [Preorder α] (x a b : α) :
--     (x ∈ Set.Ioo a b) = (let x := x; a < x ∧ x < b) := by rfl

-- @[ftrans_simp]
-- theorem _root_.Set.mem_Icc' {α} [Preorder α] (x a b : α) :
--     (x ∈ Set.Icc a b) = (let x := x; a ≤ x ∧ x ≤ b) := by rfl

-- @[ftrans_simp]
-- theorem _root_.Set.mem_Ico' {α} [Preorder α] (x a b : α) :
--     (x ∈ Set.Ico a b) = (let x := x; a ≤ x ∧ x < b) := by rfl

-- @[ftrans_simp]
-- theorem _root_.Set.mem_Ioc' {α} [Preorder α] (x a b : α) :
--     (x ∈ Set.Ioc a b) = (let x := x; a < x ∧ x ≤ b) := by rfl

-- @[ftrans_simp]
-- theorem Set.mem_inter' (x : α) (a b : Set α) : (x ∈ a ∩ b) = (let x := x; x ∈ a ∧ x ∈ b) := by rfl
