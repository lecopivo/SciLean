import SciLean.Core
import SciLean.Core.Functions.Exp
import SciLean.Core.Meta.GenerateRevDeriv
import SciLean.Data.DataArray
import SciLean.Data.ArrayType
import SciLean.Data.Prod
import Mathlib

namespace SciLean.ML

variable 
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

def softMax
  {ι} [Index ι] (r : R) (x : R^ι) : R^ι := 
  let x := ArrayType.map (fun xi => Scalar.exp (r*xi)) x
  let w := ∑ i, x[i]
  (1/w) • x

#generate_revDeriv softMax x
  prop_by unfold softMax; fprop
  trans_by unfold softMax; ftrans

