import SciLean

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]

example
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun x' => f (ydg.1 + semiAdjoint K (ydg.2 · 0) (x' - x))) x
      zdf := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext _; 
  -- failed to synthesize
  --   SemiInnerProductSpace K (X → X)
  -- ftrans 
  sorry_proof
