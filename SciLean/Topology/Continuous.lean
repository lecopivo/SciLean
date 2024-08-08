import Mathlib.Topology.Basic

import SciLean.Util.SorryProof

@[fun_prop]
theorem _root_.dite.arg_te.Continuous_rule {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (c : Prop) [Decidable c]
    (t : c → X → Y) (ht : ∀ h, Continuous (t h))
    (e : ¬c → X → Y) (he : ∀ h, Continuous (e h)) :
    Continuous (fun x => dite c (t · x) (e · x)) := by
  split_ifs <;> fun_prop

-- Is this true? I'm not really sure.
@[fun_prop]
theorem _root_.Eq.rec.Continuous_rule {α} (X : α → Type) [∀ a, TopologicalSpace (X a)] (a a' : α) (h : a = a') :
  Continuous (fun x : X a => h ▸ x) := sorry_proof
