import SciLean

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]

-- example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, IsDifferentiable K (f · i j k))
--   : IsDifferentiable K f := by fprop

-- example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, IsDifferentiable K (f · i j k))
--   : IsDifferentiable K (fun x => f x i j) := by fprop

-- example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, IsDifferentiable K (f · i j k))
--   : IsDifferentiable K (fun x => f x) := by fprop

-- example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, IsDifferentiable K (f · i j k))
--   : IsDifferentiable K (fun x i j => f x i j) := by fprop

-- example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, IsDifferentiable K (f · i j k))
--   : IsDifferentiable K (fun x i j k => f x i j k) := by fprop


example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : IsDifferentiable K f) (i j k)
  : IsDifferentiable K (fun x => f x i j k) := by fprop


example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : IsDifferentiable K f) (j k)
  : IsDifferentiable K (fun x i => f x i j k) := by fprop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : IsDifferentiable K f) (j)
  : IsDifferentiable K (fun x i k => f x i j k) := by fprop
