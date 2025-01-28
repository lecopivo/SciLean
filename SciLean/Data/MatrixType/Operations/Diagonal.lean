import SciLean.Data.MatrixType.Operations.ToMatrix
import SciLean.Data.MatrixType.Square

namespace SciLean

open MatrixType

open Classical in
def_fun_prop diagonal in x [VectorType.Lawful M] [VectorType.Lawful X] : IsLinearMap K by
  constructor <;> (intros; apply MatrixType.toMatrix_injective; simp[matrix_to_spec,vector_to_spec])

-- def_fun_prop diagonal in x [VectorType.Lawful M] [VectorType.Lawful X] : IsContinuousLinearMap K by
--   constructor
--   · fun_prop
--   ·
