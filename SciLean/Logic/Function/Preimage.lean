import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image

import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Elab

import SciLean.Analysis.Scalar
import SciLean.Util.SorryProof

variable {α β γ : Type _}

attribute [fun_trans] Set.preimage
attribute [fun_trans] Set.image

attribute [fun_trans] Set.preimage_id Set.preimage_id'

namespace Set

/-- Take a slice of a set in the first component. -/
def fst (A : Set (α×β)) (b : β) : Set α := {x | (x,b) ∈ A}

/-- Take a slice of a set in the second component. -/
def snd (A : Set (α×β)) (a : α) : Set β := {y | (a,y) ∈ A}


@[simp, simp_core]
theorem mem_fst (x : α) (b : β) (A : Set (α×β)) : (x ∈ A.fst b) = ((x,b) ∈ A) := by rfl

@[simp, simp_core]
theorem mem_snd (a : α) (y : β) (A : Set (α×β)) : (y ∈ A.snd a) = ((a,y) ∈ A) := by rfl


----------------------------------------------------------------------------------------------------

open Classical in
@[fun_trans]
theorem preimage_const' (b : β) (s : Set β) :
    (fun _ : α => b) ⁻¹' s = if b ∈ s then univ else ∅ := by apply preimage_const

@[fun_trans]
theorem preimage_comp' (f : β → γ) (g : α → β) :
    preimage (fun x => f (g x))
    =
    fun s => g ⁻¹' (f ⁻¹' s) := rfl


----------------------------------------------------------------------------------------------------

@[fun_trans]
theorem Prod.mk.arg_fstsnd.preimage_rule_prod (f : α → β) (g : α → γ) (B : Set β) (C : Set γ) :
    preimage (fun x => (f x, g x)) (B.prod C)
    =
    f ⁻¹' B ∩ g ⁻¹' C := by ext; simp[Set.prod]

@[fun_trans]
theorem Prod.mk.arg_fst.preimage_rule_prod (f : α → β) (c : γ) :
    preimage (fun x => (f x, c))
    =
    fun s => f ⁻¹' (s.fst c) := by ext; simp

@[fun_trans]
theorem Prod.mk.arg_snd.preimage_rule_prod (b : β) (g : α → γ) :
    preimage (fun x => (b, g x))
    =
    fun s => g ⁻¹' (s.snd b) := by ext; simp


open SciLean
variable {R} [RealScalar R] -- probably generalize following to LinearlyOrderedAddCommGroup

@[fun_trans]
theorem HAdd.hAdd.arg_a0.preimage_rule_Ioo (x' a b : R) :
    preimage (fun x : R => x + x') (Ioo a b)
    =
    Ioo (a - x') (b - x') := by ext; simp; sorry_proof -- over ℝ `simp` finishes the proof

@[fun_trans]
theorem HAdd.hAdd.arg_a1.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x' + x) (Ioo a b)
    =
    Ioo (a - x') (b - x') := by ext; simp; sorry_proof -- over ℝ `simp` finishes the proof

@[fun_trans]
theorem HSub.hSub.arg_a0.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x - x') (Ioo a b)
    =
    Ioo (a + x') (b + x') := by ext; simp; sorry_proof -- over ℝ `simp` finishes the proof

@[fun_trans]
theorem HSub.hSub.arg_a1.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x' - x) (Ioo a b)
    =
    Ioo (x' - b) (x' - a) := by ext; simp; sorry_proof -- over ℝ `simp` finishes the proof

@[fun_trans]
theorem Neg.neg.arg_a1.preimage_rule_Ioo (a b : R)  :
    preimage (fun x : R => - x) (Ioo a b)
    =
    Ioo (-b) (-a) := by ext; simp; sorry_proof -- over ℝ `simp` finishes the proof
