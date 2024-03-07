import SciLean.Util.SorryProof
import SciLean.Util.Impl

namespace SciLean

/-- Value of a given type but its run time value has been erased. -/
structure RunTimeErased (α) where
  P : α → Prop
  ex : ∃ a, P a
  uniq : ∀ a a', P a → P a' → a = a'

def erase {α} (a : α) : RunTimeErased α :=
  { P := fun x => x = a
    ex := Exists.intro a rfl
    uniq := by intro a b h h'; simp[h,h']
  }

noncomputable
def RunTimeErased.val {α} (a : RunTimeErased α) : α := Classical.choose a.ex

@[simp]
theorem val_erase (a : α) : (erase a).val = a := by sorry_proof

instance : Coe α (RunTimeErased α) := ⟨fun a => erase a⟩
noncomputable
instance : Coe (RunTimeErased α) α := ⟨fun e => e.val⟩
noncomputable
instance : CoeFun (RunTimeErased (α→β)) (fun _ => α → β) := ⟨fun e => e.val⟩
