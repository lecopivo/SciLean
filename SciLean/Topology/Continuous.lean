module

public import Mathlib.Topology.Basic

public import SciLean.Util.SorryProof

@[expose] public section


@[fun_prop]
theorem _root_.dite.arg_te.Continuous_rule {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (c : Prop) [Decidable c]
    (t : c → X → Y) (ht : ∀ h, Continuous (t h))
    (e : ¬c → X → Y) (he : ∀ h, Continuous (e h)) :
    Continuous (fun x => dite c (t · x) (e · x)) := by
  split_ifs <;> fun_prop

@[fun_prop]
theorem _root_.Eq.rec.Continuous_rule {α} (X : α → Type) [∀ a, TopologicalSpace (X a)] (a a' : α) (h : a = a') :
  Continuous (fun x : X a => h ▸ x) := by cases h; exact ⟨fun s hs => by simpa using hs⟩
