import SciLean.Data.EnumType

namespace SciLean

variable {ι} [EnumType ι]

@[simp]
theorem sum_if {β : Type _} [AddCommMonoid β] (f : ι → β)  (j : ι)
  : (∑ i, if i = j then f i else 0)
    =
    f j
  := sorry_proof

@[simp]
theorem sum_if' {β : Type _} [AddCommMonoid β] (f : ι → β)  (j : ι)
  : (∑ i, if j = i then f i else 0)
    =
    f j
  := sorry_proof

@[simp]
theorem sum_lambda_swap {α β : Type _} [AddCommMonoid β] (f : ι → α → β) 
  : ∑ i, (fun a => f i a)
    =
    fun a => ∑ i, f i a
  := sorry_proof

