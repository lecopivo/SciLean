import SciLean.Data.EnumType

namespace SciLean

variable {ι κ} [EnumType ι] [EnumType κ]

-- @[simp]
-- theorem sum_if {β : Type _} [AddCommMonoid β] (f : ι → β)  (j : ι)
--   : (∑ i, if i = j then f i else 0)
--     =
--     f j
--   := sorry_proof

-- @[simp]
-- theorem sum_if' {β : Type _} [AddCommMonoid β] (f : ι → β)  (j : ι)
--   : (∑ i, if j = i then f i else 0)
--     =
--     f j
--   := sorry_proof

-- @[simp]
-- theorem sum_lambda_swap {α β : Type _} [AddCommMonoid β] (f : ι → α → β) 
--   : ∑ i, (fun a => f i a)
--     =
--     fun a => ∑ i, f i a
--   := sorry_proof


-- @[simp]
-- theorem sum2_if {β : Type _} [AddCommMonoid β] (f : ι → κ → β) (ij : ι×κ)
--   : (∑ i, ∑ j, if ij = (i,j) then f i j else 0)
--     =
--     f ij.1 ij.2
--   := sorry_proof

-- @[simp]
-- theorem sum2'_if {β : Type _} [AddCommMonoid β] (f : ι → κ → β) (ij : ι×κ)
--   : (∑ j, ∑ i, if ij = (i,j) then f i j else 0)
--     =
--     f ij.1 ij.2
--   := sorry_proof


-- @[simp]
-- theorem sum2_if' {β : Type _} [AddCommMonoid β] (f : ι → κ → β) (ij : ι×κ)
--   : (∑ i, ∑ j, if (i,j) = ij then f i j else 0)
--     =
--     f ij.1 ij.2
--   := sorry_proof

-- @[simp]
-- theorem sum2'_if' {β : Type _} [AddCommMonoid β] (f : ι → κ → β) (ij : ι×κ)
--   : (∑ j, ∑ i, if (i,j) = ij then f i j else 0)
--     =
--     f ij.1 ij.2
--   := sorry_proof
