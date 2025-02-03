import SciLean.Meta.SimpAttr

namespace SciLean

@[simp, simp_core]
theorem Prod.snd_ite {c : Prop} [Decidable c] (t e : α×β) :
    (if c then t else e).2 = if c then t.2 else e.2 :=
  by by_cases h : c <;> simp[h]

@[simp, simp_core]
theorem Prod.fst_ite {c : Prop} [Decidable c] (t e : α×β) :
    (if c then t else e).2 = if c then t.2 else e.2 :=
  by by_cases h : c <;> simp[h]
