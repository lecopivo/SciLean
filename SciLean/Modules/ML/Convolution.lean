import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.ArrayType
import SciLean.Data.Prod

namespace SciLean.ML

set_option synthInstance.maxSize 2000

variable
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

def conv2d
  {n m : USize} {ι} [IndexType ι] (filterNum : Nat) (r : Int64)
  (weights : R^[filterNum, [-r:r], [-r:r]]) (bias x : R^[ι,n,m]) : R^[[filterNum,ι],n,m] :=
  ⊞ ((k,l),i,j) =>
    bias[(l,i,j)]
    +
    ∑ i' j', weights[(k,i',j')] * x[(l, i'.1 +ᵥ i, j'.1 +ᵥ j)]

#generate_revDeriv conv2d weights bias x
  prop_by unfold conv2d; fprop
  trans_by unfold conv2d; ftrans
