import Mathlib.Logic.Function.Defs

namespace SciLean


open Function
class InjectiveGetElem (coll : Type*) (idx : Type*) {elem : outParam Type*}
    [GetElem coll idx elem (fun _ _ => True)] : Prop where
  getElem_injective : Injective ((getElem · · .intro) : coll → idx → elem)

export InjectiveGetElem (getElem_injective)

class SetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
              (valid : outParam (coll → idx → Prop)) where
  setElem (xs : coll) (i : idx) (v : elem) (h : valid xs i) : coll
  setElem_valid {xs : coll} {i j : idx} {v : elem} {hi : valid xs i} (hj : valid xs j) :
    valid (setElem xs i v hi) j

export SetElem (setElem setElem_valid)

attribute [simp] setElem_valid

open SetElem
class LawfulSetElem (coll : Type u) (idx : Type v)
    {elem : outParam (Type w)} {valid : outParam (coll → idx → Prop)}
    [SetElem coll idx elem valid] [GetElem coll idx elem valid] : Prop where
  getElem_setElem_eq (xs : coll) (i : idx) (v : elem) (h : valid xs i) :
    getElem (setElem xs i v h) i (setElem_valid h) = v
  getElem_setElem_neq (xs : coll) (i j : idx) (v : elem) (hi : valid xs i) (hj : valid xs j) :
    i≠j → getElem (setElem xs i v hi) j (setElem_valid hj) = getElem xs j hj

export LawfulSetElem (getElem_setElem_eq getElem_setElem_neq)

attribute [simp] getElem_setElem_eq getElem_setElem_neq

class ArrayLike (coll : Type u) (idx : Type v) (elem : outParam (Type w)) extends
   GetElem coll idx elem (fun _ _ => True),
   SetElem coll idx elem (fun _ _ => True)

class LawfulArrayLike (coll : Type u) (idx : Type v) (elem : outParam (Type w))
      [ArrayLike coll idx elem] extends
   InjectiveGetElem coll idx,
   LawfulSetElem coll idx : Prop
