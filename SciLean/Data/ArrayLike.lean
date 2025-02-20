import Mathlib.Logic.Function.Defs
import SciLean.Meta.SimpAttr

namespace SciLean


open Function
/-- Type `coll` is fully determined by all its elements accesible with index notation `x[i]`.

This gives us extensionality property `(∀ i, x[i] = y[i]) → x = y` which is accessible with
`ext` tactic if also `coll` defines default index type with `DefaultIndex`
-/
class InjectiveGetElem (coll : Type*) (idx : Type*) {elem : outParam Type*}
    [GetElem coll idx elem (fun _ _ => True)] : Prop where
  getElem_injective : Injective ((getElem · · .intro) : coll → idx → elem)

/-- Default index type of `coll` is `idx`. This class is used when elaborating `x[i]` where `i`
has  unknown type. -/
class DefaultIndex (coll : Type*) (idx : outParam Type*) where

export InjectiveGetElem (getElem_injective)

@[ext]
theorem getElem_ext {coll idx elem : Type*}
    [GetElem coll idx elem (fun _ _ => True)] [DefaultIndex coll idx] [InjectiveGetElem coll idx]
    (x y : coll) :
    (∀ i : idx, x[i] = y[i]) → x = y := by
  intro h; apply getElem_injective (idx:=idx); funext i; exact h i

class SetElem (coll : Type u) (idx : Type v) (elem : outParam (Type w))
              (valid : outParam (coll → idx → Prop)) where
  setElem (xs : coll) (i : idx) (v : elem) (h : valid xs i) : coll
  setElem_valid {xs : coll} {i j : idx} {v : elem} {hi : valid xs i} (hj : valid xs j) :
    valid (setElem xs i v hi) j

export SetElem (setElem setElem_valid)

attribute [simp, simp_core] setElem_valid

open SetElem
class LawfulSetElem (coll : Type u) (idx : Type v)
    {elem : outParam (Type w)} {valid : outParam (coll → idx → Prop)}
    [SetElem coll idx elem valid] [GetElem coll idx elem valid] : Prop where
  getElem_setElem_eq (xs : coll) (i : idx) (v : elem) (h : valid xs i) :
    getElem (setElem xs i v h) i (setElem_valid h) = v
  getElem_setElem_neq (xs : coll) (i j : idx) (v : elem) (hi : valid xs i) (hj : valid xs j) :
    i≠j → getElem (setElem xs i v hi) j (setElem_valid hj) = getElem xs j hj

export LawfulSetElem (getElem_setElem_eq getElem_setElem_neq)

attribute [simp, simp_core] getElem_setElem_eq getElem_setElem_neq

class ArrayLike (coll : Type u) (idx : Type v) (elem : outParam (Type w)) extends
   GetElem coll idx elem (fun _ _ => True),
   SetElem coll idx elem (fun _ _ => True)

class LawfulArrayLike (coll : Type u) (idx : Type v) (elem : outParam (Type w))
      [ArrayLike coll idx elem] extends
   InjectiveGetElem coll idx,
   LawfulSetElem coll idx : Prop

class OfFn (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  ofFn (f : idx → elem) : coll

export OfFn (ofFn)

class LawfulOfFn (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [OfFn coll idx elem] [GetElem coll idx elem (fun _ _ => True)] where
  getElem_ofFn (f : idx → elem) (i : idx) : (ofFn (coll:=coll) f)[i] = f i

export LawfulOfFn (getElem_ofFn)

attribute [simp, simp_core] getElem_ofFn

/-- This class indicates that `ofFn f` for `f : idx → elem` should create somethig of type `coll`.

This class is use to infer the default type of `⊞ i => f i` notation. -/
class DefaultCollection (coll : outParam Type*) (idx : Type*) (elem : Type*) where

theorem ofFn_rightInverse
    (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem coll idx elem (fun _ _ => True)] [OfFn coll idx elem] [LawfulOfFn coll idx] :
    RightInverse (ofFn : (idx → elem) → coll) (fun (x : coll) (i : idx) => x[i]) := by
  intro f; funext i; simp

theorem ofFn_injective
    (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem coll idx elem (fun _ _ => True)] [InjectiveGetElem coll idx]
    [OfFn coll idx elem] [LawfulOfFn coll idx] :
    Function.Surjective (ofFn : (idx → elem) → coll) := by
  intro x
  apply Exists.intro (fun i => x[i])
  apply getElem_injective (idx:=idx)
  simp

theorem ofFn_surjective
    (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem coll idx elem (fun _ _ => True)] [InjectiveGetElem coll idx]
    [OfFn coll idx elem] [LawfulOfFn coll idx] :
    Function.Surjective (ofFn : (idx → elem) → coll) := by
  intro x
  apply Exists.intro (fun i => x[i])
  apply getElem_injective (idx:=idx)
  simp

theorem getElem_surjective (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem coll idx elem (fun _ _ => True)] [OfFn coll idx elem] [LawfulOfFn coll idx] :
    Surjective (fun (x : coll) (i : idx) => x[i]) := (ofFn_rightInverse coll idx).surjective


----------------------------------------------------------------------------------------------------
-- Instances


-- Unit
instance : GetElem α Unit α (fun _ _ => True) where
  getElem x _ _ := x

instance : InjectiveGetElem α Unit where
  getElem_injective := by intro x y h; have := congrFun h (); simp_all[getElem]

instance : OfFn α Unit α where
  ofFn f := f ()

instance : LawfulOfFn α Unit where
  getElem_ofFn := by intros; simp[getElem,ofFn]


-- Prod
instance [GetElem α ι γ (fun _ _ => True)] [GetElem β κ γ (fun _ _ => True)] :
    GetElem (α×β) (ι⊕κ) γ (fun _ _ => True) where
  getElem x i _ := match x, i with | (x,y), .inl i => x[i] | (x,y), .inr j => y[j]

instance [GetElem α ι γ (fun _ _ => True)] [GetElem β κ γ (fun _ _ => True)]
         [InjectiveGetElem α ι] [InjectiveGetElem β κ] : InjectiveGetElem (α×β) (ι⊕κ) where
  getElem_injective := by
    intro x y h
    cases x; cases y; simp
    constructor
    · apply getElem_injective (idx:=ι); funext i
      exact congrFun h (.inl i)
    · apply getElem_injective (idx:=κ); funext j
      exact congrFun h (.inr j)

instance [OfFn α ι γ] [OfFn β κ γ] : OfFn (α×β) (ι⊕κ) γ where
  ofFn f := (ofFn (fun i => f (.inl i)), ofFn (fun j => f (.inr j)))

instance [GetElem α ι γ (fun _ _ => True)] [GetElem β κ γ (fun _ _ => True)]
         [OfFn α ι γ] [OfFn β κ γ] [LawfulOfFn α ι] [LawfulOfFn β κ] :
         LawfulOfFn (α×β) (ι⊕κ) where
  getElem_ofFn := by intro f i; cases i <;> simp[getElem,ofFn]

@[simp, simp_core]
theorem getElem_prod_inl [GetElem α ι γ (fun _ _ => True)] [GetElem β κ γ (fun _ _ => True)]
        (x : α) (y : β) (i : ι) : (x,y)[Sum.inl (β:=κ) i] = x[i] := by rfl

@[simp, simp_core]
theorem getElem_prod_inr [GetElem α ι γ (fun _ _ => True)] [GetElem β κ γ (fun _ _ => True)]
        (x : α) (y : β) (j : κ) : (x,y)[Sum.inr (α:=ι) j] = y[j] := by rfl


-- Vector
instance : OfFn (Vector α n) (Fin n) α where
  ofFn := Vector.ofFn
