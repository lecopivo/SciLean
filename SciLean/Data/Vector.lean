import Mathlib.Algebra.Group.Defs

import SciLean.Data.ArrayOperations.Basic
import SciLean.Util.SorryProof

namespace SciLean

-- Array Operations

-- this is potentially evil instance as `Vector α n` already has `GetElem` but with different dom
instance : GetElem' (Vector α n) (Fin n) α where
  getElem xs i h := xs[i]

instance : DefaultIndex (Vector α n) (Fin n) where

instance : SetElem' (Vector α n) (Fin n) α where
  setElem x i v _ := x.set i v
  setElem_valid := by simp

instance : LawfulSetElem (Vector α n) (Fin n) where
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof

instance : OfFn (Vector α n) (Fin n) α where
  ofFn := Vector.ofFn

instance : LawfulOfFn (Vector α n) (Fin n) where
  getElem_ofFn := by
    simp[getElem,ofFn,Vector.ofFn]
    unfold Vector.get
    simp


-- Algebraic Operations
instance [Add X] : Add (Vector X n) := ⟨fun x y => ⟨x.mapFinIdx fun i xi => xi + y[i], by simp⟩⟩
instance [Sub X] : Sub (Vector X n) := ⟨fun x y => ⟨x.mapFinIdx fun i xi => xi - y[i], by simp⟩⟩
instance [Neg X] : Neg (Vector X n) := ⟨fun x => x.map fun xi => -xi⟩
instance [SMul R X] : SMul R (Vector X n) := ⟨fun r x => x.map fun xi => r • xi⟩
instance [Zero X] : Zero (Vector X n) := ⟨⟨Array.mkArray n (0:X), by simp⟩⟩
