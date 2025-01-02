import SciLean

open SciLean

variable
  {K : Type} [RCLike K]
  {α : Type}

example (i : α) : CDifferentiable K (fun (xy : (α → K) × (α → K)) => xy.fst i) := by fun_prop

example (i : α)
  : cderiv K (fun (xy : (α → K) × (α → K)) => xy.fst i)
    =
    fun _ dxy =>
      dxy.1 i :=
by
  conv => lhs; autodiff
