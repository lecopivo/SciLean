import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod
import Mathlib

namespace SciLean

variable 
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

def avgPool {n m : USize} {ι} [Index ι] (x : R^[ι,n,m]) : R^[ι,n/2,m/2] :=
  ⊞ (k,i,j) => (1/4 : R) * ∑ i' j' : Idx 2, x[(k, ⟨2*i.1+i'.1, sorry_proof⟩, ⟨2*j.1+j'.1,sorry_proof⟩)]

#generate_revDeriv avgPool x
  prop_by unfold avgPool; fprop
  trans_by unfold avgPool; ftrans


-- TODO: needs exp and division working
-- def softMaxPool {n m : USize} {ι} [Index ι] (scale : R) (x : R^[ι,n,m]) : R^[ι,n/2,m/2] :=
--   introElem fun (k,i,j) =>
--     let a := x[(k,⟨2*i.1  ,sorry_proof⟩, ⟨2*j.1  ,sorry_proof⟩)]
--     let b := x[(k,⟨2*i.1  ,sorry_proof⟩, ⟨2*j.1+1,sorry_proof⟩)]
--     let c := x[(k,⟨2*i.1+1,sorry_proof⟩, ⟨2*j.1+1,sorry_proof⟩)]
--     let d := x[(k,⟨2*i.1+1,sorry_proof⟩, ⟨2*j.1+1,sorry_proof⟩)]
--     let ea := Scalar.exp (scale*a)
--     let eb := Scalar.exp (scale*b)
--     let ec := Scalar.exp (scale*c)
--     let ed := Scalar.exp (scale*d)
--     have : (ea + eb + ec + ed) ≠ 0 := sorry_proof
--     let w := 1 / (ea + eb + ec + ed)
--     (a*ea+b*eb+c*ec+d*ed) * w



