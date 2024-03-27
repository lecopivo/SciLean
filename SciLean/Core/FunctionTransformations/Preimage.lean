import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Image

import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Elab

import SciLean.Core.Objects.Scalar
import SciLean.Util.SorryProof

variable {α β γ : Type _}

attribute [fun_trans] Set.preimage
attribute [fun_trans] Set.image


attribute [fun_trans] Set.preimage_id
-- attribute [fun_trans]

namespace Set

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
    f ⁻¹' B ∩ g ⁻¹' C := sorry_proof

open SciLean
variable {R} [RealScalar R] -- probably generalize following to LinearlyOrderedAddCommGroup

@[fun_trans]
theorem HAdd.hAdd.arg_a0.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x + x') (Ioo a b)
    =
    Ioo (a - x') (b - x') := by ext; simp; sorry_proof

@[fun_trans]
theorem HAdd.hAdd.arg_a1.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x' + x) (Ioo a b)
    =
    Ioo (a - x') (b - x') := by ext; simp; sorry_proof

@[fun_trans]
theorem HSub.hSub.arg_a0.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x - x') (Ioo a b)
    =
    Ioo (a + x') (b + x') := by ext; simp; sorry_proof

@[fun_trans]
theorem HSub.hSub.arg_a1.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => x' - x) (Ioo a b)
    =
    Ioo (x' - b) (x' - a) := by ext; simp; sorry_proof

@[fun_trans]
theorem Neg.neg.arg_a1.preimage_rule_Ioo (x' a b : R)  :
    preimage (fun x : R => - x) (Ioo a b)
    =
    Ioo (-b) (-a) := by ext; simp; sorry_proof
