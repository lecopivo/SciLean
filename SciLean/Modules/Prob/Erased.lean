import Batteries

structure Erased (α : Type) : Type where
  spec : α → Prop
  ex : ∃ a, spec a
  uniq : ∀ a b, spec a → spec b → a = b

@[coe]
noncomputable
def Erased.get (x : Erased α) : α := Classical.choose x.ex

def erase (x : α) : Erased α where
  spec := Eq x
  ex := ⟨x, rfl⟩
  uniq := by intro a b h h'; rw[← h,h']

@[ext]
theorem Erased.ext (x y : Erased α) : x.get = y.get → x = y := sorry

noncomputable
instance : Coe (Erased α) α where
  coe x := x.get

@[simp]
theorem Erased.erase_get (x : α) : (erase x).get = x := sorry
