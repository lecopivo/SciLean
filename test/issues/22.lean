import SciLean.Core.FunctionTransformations.CDeriv

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {α : Type _}

example (i : α) : IsDifferentiable K (fun (xy : (α → K) × (α → K)) => xy.fst i) := by fprop

example (i : α) 
  : cderiv K (fun (xy : (α → K) × (α → K)) => xy.fst i)
    =
    fun _ dxy => 
      dxy.1 i := 
by 
  ftrans only
  
