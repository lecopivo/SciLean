import SciLean.Data.DataArray.Operations.Matmul

namespace SciLean

open DataArrayN

def_fun_prop npow in A with_transitive : Differentiable R by
  induction' n
  case zero => simp[npow]
  case succ n' hn' =>
  have hn : ∀ m, (m ≤ n') → Differentiable R (fun (A : R^[I,I]) => A.npow m) := sorry_proof
  induction n'
  case zero => simp[npow]
  case succ n'' _ =>
    unfold npow
    fun_prop (disch:=omega)
