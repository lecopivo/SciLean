import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Nat

import SciLean.Util.SorryProof

namespace SciLean

open Classical in
/-- Returns permutation of indices `I` under which `x : I → X` is sorted.

--TODO: note implementations of this function
-/
noncomputable
def sortPermutation {I X} [PartialOrder I] [PartialOrder X] (x : I → X) : I ≃ I :=
  if h : ∃ p : I ≃ I, ∀ i j, i ≤ j → x (p i) ≤ x (p j) then
     choose h
  else
    Equiv.refl I


/-- Returns permuation of indices under which the array is sorted. -/
def _root_.Array.qsortPermutation [LinearOrder X] (xs : Array X) : Fin xs.size ≃ Fin xs.size :=

  let n := xs.size
  let xs := xs.mapFinIdx (fun i x h => ((⟨i,h⟩ : Fin _),x))
  let xs := xs.qsort (fun (_,x) (_,x') => x < x')
  let (is,_) := xs.unzip
  let is : Array (Fin n) := cast sorry_proof is
  let js := is.foldl (init:=Array.finRange n)
    (fun js i =>
      let i' := is[i.1]'sorry_proof
      js.set i' i sorry_proof)

  {
    toFun := fun i => is[i]'sorry_proof
    invFun := fun j => js[j]'sorry_proof
    left_inv := sorry_proof
    right_inv := sorry_proof
  }


/-- Returns permuation of indices under which the vector is sorted. -/
def _root_.Vector.qsortPermutation {n : ℕ} [LinearOrder X] (xs : Vector X n) :
    Fin n ≃ Fin n :=
  let P := xs.toArray.qsortPermutation
  cast (by simp[xs.2]) P
