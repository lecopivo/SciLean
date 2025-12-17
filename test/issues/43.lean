import SciLean

open SciLean

variable {R} [RealScalar R] [PlainDataType R] (n : Nat) [BLAS (DataArray R) R R] [LawfulBLAS (DataArray R) R R]


-- We gave up on revFDerivProj
-- -- This should be fixed!!!
-- /--
-- info: revFDerivProj R (Fin n × Unit) fun f => ⊞ i => f i : (Fin n → R) → R^[n] × (Fin n × Unit → R → Fin n → R)
-- -/
-- #guard_msgs in
-- #check (revFDerivProj R (Fin n × Unit) (fun f : Fin n → R => ⊞ i => f i)) rewrite_by
--   autodiff
