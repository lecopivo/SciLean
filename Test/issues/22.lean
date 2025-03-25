import SciLean

open SciLean

variable
  {K : Type} [RCLike K]
  {α : Type} [Fintype α]


example (i : α) : Differentiable K (fun (xy : (α → K) × (α → K)) => xy.fst i) := by fun_prop

example (i : α)
  : fderiv K (fun (xy : (α → K) × (α → K)) => xy.fst i)
    =
    fun _ => fun dxy =>L[K]
      dxy.1 i :=
by
  conv => lhs; fun_trans
