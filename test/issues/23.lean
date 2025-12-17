import SciLean

open SciLean

variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]


example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, Differentiable K (f · i j k))
  : Differentiable K f := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, Differentiable K (f · i j k))
  : Differentiable K (fun x => f x i j) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, Differentiable K (f · i j k))
  : Differentiable K (fun x => f x) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, Differentiable K (f · i j k))
  : Differentiable K (fun x i j => f x i j) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, Differentiable K (f · i j k))
  : Differentiable K (fun x i j k => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j, Differentiable K (f · i j))
  : Differentiable K (fun x i => f x i) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j, Differentiable K (f · i j)) (j k)
  : Differentiable K (fun x i => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : Differentiable K f) (i j k)
  : Differentiable K (fun x => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : Differentiable K f) (j k)
  : Differentiable K (fun x i => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : Differentiable K f) (j)
  : Differentiable K (fun x i k => f x i j k) := by fun_prop
