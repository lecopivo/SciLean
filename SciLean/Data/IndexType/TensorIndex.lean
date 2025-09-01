import SciLean.Data.IndexType.Basic
import SciLean.Data.IndexType.SumProduct

import Mathlib.Logic.Equiv.Fin.Basic

namespace SciLean

/-- IndexType `I` is tensor index of rank `rank` i.e.  -/
class TensorIndex (I : Type*) (rank : outParam ℕ) {nI} [IndexType I nI] where
  valid : (Fin rank → ℕ) → Prop
  equiv : I ≃ {idx : Fin rank → ℕ // valid idx}
  strides : Fin rank → ℕ
  equiv_toFin (i : I) : (IndexType.toFin i).1 = ∑ (d : Fin rank), (equiv i).1 d * strides d


-- instance : TensorIndex (Fin n) 1 where
--   valid i := i 0 < n
--   equiv := {
--       toFun i := ⟨fun _ => i, by have := i.2; simp⟩
--       invFun i := ⟨i.1 0, i.2⟩
--       left_inv := by intro x; simp
--       right_inv := by intro i; ext d; simp; apply congrArg; aesop
--     }
--   strides := fun _ => 1
--   equiv_toFin := by intro i; simp[Finset.sum,sum_to_finset_sum]

-- def finProdArrowEquiv {α : Type*} {m n : ℕ} : (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α) :=
--   let g : ((Fin m → α) × (Fin n → α)) ≃ (Fin m ⊕ Fin n → α) := (Equiv.sumArrowEquivProdArrow _ _ _).symm
--   let f : (Fin m ⊕ Fin n → α) ≃ (Fin (m+n) → α):= Equiv.arrowCongr finSumFinEquiv (Equiv.refl α)
--   g.trans f

-- instance
--     {I J} [IndexType I] [IndexType J]
--     [ti : TensorIndex I r] [tj : TensorIndex J s] :
--     TensorIndex (I×J) (r+s) where
--   valid := fun i =>
--     let (i,j) := (finProdArrowEquiv.symm i)
--     ti.valid i ∧ tj.valid j
--   equiv := {
--       toFun := fun (i,j) =>
--         ⟨fun d => (finSumFinEquiv.symm d).elim (ti.equiv i).1 (tj.equiv j).1 , by sorry_proof⟩
--       invFun idx :=
--         let i := (finProdArrowEquiv.symm idx.1).1
--         let j := (finProdArrowEquiv.symm idx.1).2
--         let i := ti.equiv.symm ⟨i,idx.2.1⟩
--         let j := tj.equiv.symm ⟨j,idx.2.2⟩
--         (i,j)
--       left_inv := by intro x; simp; sorry_proof
--       right_inv := by intro i; ext d; simp; sorry_proof
--     }
--   strides :=
--     -- Row major ordering - this should be consistent with
--     finProdArrowEquiv (fun d => size J * ti.strides d, tj.strides)
--   equiv_toFin := by
--     rintro ⟨i,j⟩
--     simp [IndexType.toFin]
--     simp [ti.equiv_toFin, tj.equiv_toFin]
--     sorry_proof
