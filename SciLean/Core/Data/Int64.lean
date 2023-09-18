import SciLean.Core.FunctionTransformations
import SciLean.Core.FunctionPropositions
import SciLean.Data.Int64

namespace SciLean

instance : AddGroup Int64 where
  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  add_left_neg := sorry_proof
  sub_eq_add_neg := sorry_proof
  
