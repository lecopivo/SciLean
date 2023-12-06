import SciLean.Core
import SciLean.Core.Functions.Exp
import SciLean.Data.DataArray
import SciLean.Data.ArrayType
import SciLean.Data.Prod
import Mathlib

namespace SciLean.ML

set_option synthInstance.maxSize 200000

variable 
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R


def _root_.SciLean.Idx.prodMerge (i : Idx (n/m)) (j : Idx m) : Idx n := ⟨i.1 * m + j.1, sorry_proof⟩
def _root_.SciLean.Idx.prodMerge' (i : Idx (n/m)) (j : Idx m) : Idx n := ⟨i.1 + j.1 * (n/m), sorry_proof⟩


def avgPool {n m : USize} {ι} [Index ι] (x : R^[ι,n,m]) : R^[ι,n/2,m/2] :=
  ⊞ (k,i,j) => (1/4 : R) * ∑ i' j' : Idx 2, x[(k,i.prodMerge i', j.prodMerge j')]

#generate_revDeriv avgPool x
  prop_by unfold avgPool; fprop
  trans_by unfold avgPool; ftrans


def softMaxPool {n m : USize} {ι} [Index ι] (scale : R) (x : R^[ι,n,m]) : R^[ι,n/2,m/2] :=
  introElem fun (k,i,j) =>
    let ex := ⊞ (ij : Idx 2 × Idx 2) => Scalar.exp (scale*x[(k, i.prodMerge ij.1, j.prodMerge ij.2)])
    let w := ∑ i', ex[i']
    let w' := 1/w
    ∑ i' j' : Idx 2, 
      let xi := x[(k, i.prodMerge i', j.prodMerge j')]
      let exi := ex[(i',j')]
      xi * (w'*exi)


#generate_revDeriv softMaxPool x
  prop_by unfold softMaxPool; fprop
  trans_by unfold softMaxPool; ftrans

