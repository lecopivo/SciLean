module

public import Mathlib.Topology.Basic

public import SciLean.Analysis.AdjointSpace.Basic
public import SciLean.Analysis.Scalar

@[expose] public section



namespace SciLean

variable
  {X} [TopologicalSpace X]



class Transform {S} (f : X → X) (set : S → Set X) where
  transform : S → S
  is_transform : ∀ (s : S) (x : X), x ∈ set s ↔ f x ∈ set (transform s)


abbrev Translate [Add X] (t : X) (set : S → Set X) := Transform (fun x => x + t) set
abbrev Reflect [Neg X] (set : S → Set X) := Transform (fun x => -x) set
