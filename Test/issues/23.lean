import SciLean

open SciLean

variable
  {K : Type _} [RCLike K]
  {X : Type _} [Vec K X]


example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, CDifferentiable K (f · i j k))
  : CDifferentiable K f := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, CDifferentiable K (f · i j k))
  : CDifferentiable K (fun x => f x i j) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, CDifferentiable K (f · i j k))
  : CDifferentiable K (fun x => f x) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, CDifferentiable K (f · i j k))
  : CDifferentiable K (fun x i j => f x i j) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j k, CDifferentiable K (f · i j k))
  : CDifferentiable K (fun x i j k => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j, CDifferentiable K (f · i j))
  : CDifferentiable K (fun x i => f x i) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : ∀ i j, CDifferentiable K (f · i j)) (j k)
  : CDifferentiable K (fun x i => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : CDifferentiable K f) (i j k)
  : CDifferentiable K (fun x => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : CDifferentiable K f) (j k)
  : CDifferentiable K (fun x i => f x i j k) := by fun_prop

example (f : X → Fin 5 → Fin 10 → Fin 15→ K) (hf : CDifferentiable K f) (j)
  : CDifferentiable K (fun x i k => f x i j k) := by fun_prop
