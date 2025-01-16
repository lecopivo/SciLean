import SciLean.Data.MatrixType.Base
import SciLean.Analysis.Calculus.RevFDeriv
import SciLean.Analysis.Calculus.FwdFDeriv
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate

namespace SciLean

#exit

theorem differentiable_iff_toVec_differentiable
  {R K} {_ : RealScalar R} {_ : Scalar R K}
  {n} {_ : IndexType n}
  {X} [VectorType.Base X n K] [VectorType.Lawful X]
  {W} [NormedAddCommGroup W] [NormedSpace K W]
  {f : W → X} :
  Differentiable K f ↔ Differentiable K (fun w => VectorType.toVec (f w)) := sorry_proof

def_fun_prop MatrixType.Base.gemv in alpha beta A x y
    [MatrixType.Lawful M] [VectorType.Lawful X] [VectorType.Lawful Y] :
    Differentiable K by
  apply differentiable_iff_toVec_differentiable.2
  simp +unfoldPartialApp [matrix_to_spec,vector_to_spec,Matrix.mulVec,dotProduct]
  fun_prop
  sorry
