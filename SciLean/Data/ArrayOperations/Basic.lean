import Mathlib.Logic.Function.Defs
import SciLean.Meta.SimpAttr
import SciLean.Lean.Expr
import SciLean.Util.SorryProof

namespace SciLean


/-- Abbreviation for `GetElem coll idx elem (fun _ _ => True)` -/
abbrev GetElem' (coll : Type*) (idx : Type*) (elem : outParam Type*) :=
  GetElem coll idx elem (fun _ _ => True)

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

class DefaultIndexOfRank (coll : Type*) (r : Nat) (idx : outParam Type*) where

/-- Index under which we can access `coll` and get elements of type `elem`. -/
class ValueIndex (coll elem : Type*) (idx : outParam Type*) where

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
  setElem_valid {xs : coll} {i j : idx} {v : elem} {hi : valid xs i} :
    valid xs j ↔ valid (setElem xs i v hi) j

/-- Abbreviation for `SetElem coll idx elem (fun _ _ => True)` -/
abbrev SetElem' (coll : Type*) (idx : Type*) (elem : outParam Type*) :=
  SetElem coll idx elem (fun _ _ => True)

export SetElem (setElem setElem_valid)

open SetElem
class LawfulSetElem (coll : Type u) (idx : Type v)
    {elem : outParam (Type w)} {valid : outParam (coll → idx → Prop)}
    [SetElem coll idx elem valid] [GetElem coll idx elem valid] : Prop where
  getElem_setElem_eq (xs : coll) (i : idx) (v : elem) (h : valid xs i) :
    getElem (setElem xs i v h) i (setElem_valid.1 h) = v
  getElem_setElem_neq (xs : coll) (i j : idx) (v : elem) (hi : valid xs i) (hj) :
    i≠j → getElem (setElem xs i v hi) j (hj) = getElem xs j (setElem_valid.2 hj)

export LawfulSetElem (getElem_setElem_eq getElem_setElem_neq)

attribute [simp, simp_core] getElem_setElem_eq getElem_setElem_neq

@[simp, simp_core]
theorem getElem_setElem (coll idx elem : Type*) (valid)
    [GetElem coll idx elem valid] [SetElem coll idx elem valid] [LawfulSetElem coll idx]
    [DecidableEq idx]
    (xs : coll) (i j : idx) (v : elem) (hi hj) :
    getElem (setElem xs i v hi) j hj = if i=j then v else getElem xs j (setElem_valid.2 hj) := by
  by_cases (i=j) <;> simp_all

class ArrayLike (coll : Type u) (idx : Type v) (elem : outParam (Type w)) extends
   GetElem' coll idx elem,
   SetElem' coll idx elem

class LawfulArrayLike (coll : Type u) (idx : Type v) (elem : outParam (Type w))
      [ArrayLike coll idx elem] : Prop extends
   InjectiveGetElem coll idx,
   LawfulSetElem coll idx

class OfFn (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  ofFn (f : idx → elem) : coll

export OfFn (ofFn)

class LawfulOfFn (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [OfFn coll idx elem] [GetElem' coll idx elem] where
  getElem_ofFn (f : idx → elem) (i : idx) : (ofFn (coll:=coll) f)[i] = f i

export LawfulOfFn (getElem_ofFn)

attribute [simp, simp_core] getElem_ofFn

/-- This class indicates that `ofFn f` for `f : idx → elem` should create somethig of type `coll`.

This class is use to infer the default type of `⊞ i => f i` notation. -/
class DefaultCollection (coll : outParam Type*) (idx : Type*) (elem : Type*) where

theorem ofFn_rightInverse
    (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem' coll idx elem] [OfFn coll idx elem] [LawfulOfFn coll idx] :
    RightInverse (ofFn : (idx → elem) → coll) (fun (x : coll) (i : idx) => x[i]) := by
  intro f; funext i; simp

theorem ofFn_injective
    (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem' coll idx elem] [InjectiveGetElem coll idx]
    [OfFn coll idx elem] [LawfulOfFn coll idx] :
    Function.Surjective (ofFn : (idx → elem) → coll) := by
  intro x
  apply Exists.intro (fun i => x[i])
  apply getElem_injective (idx:=idx)
  simp

theorem ofFn_surjective
    (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem' coll idx elem] [InjectiveGetElem coll idx]
    [OfFn coll idx elem] [LawfulOfFn coll idx] :
    Function.Surjective (ofFn : (idx → elem) → coll) := by
  intro x
  apply Exists.intro (fun i => x[i])
  apply getElem_injective (idx:=idx)
  simp

theorem getElem_surjective (coll : Type u) (idx : Type v) {elem : outParam (Type w)}
    [GetElem' coll idx elem] [OfFn coll idx elem] [LawfulOfFn coll idx] :
    Surjective (fun (x : coll) (i : idx) => x[i]) := (ofFn_rightInverse coll idx).surjective



----------------------------------------------------------------------------------------------------
-- (Un)curry element access ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Compatibilty class saying `x[i,j] = x[i][j]`. -/
class IsGetElemCurry (X : Type*) {Y Z : Type*} (I J : Type*)
    [GetElem' X I Y] [GetElem' X (I×J) Z] [GetElem' Y J Z] : Prop where
  getElem_curry : ∀ (x : X) (ij : I×J), x[ij] = x[ij.1][ij.2]

export IsGetElemCurry (getElem_curry)

theorem getElem_uncurry {X Y Z I J : Type*}
    [GetElem' X I Y] [GetElem' X (I×J) Z] [GetElem' Y J Z] [h : IsGetElemCurry X I J]
    (x : X) (i : I) (j : J) : x[i][j] = x[(i,j)] := by
  rw [h.getElem_curry]

@[simp, simp_core]
theorem getElem_ofFn_curry
    [GetElem' X I Y] [GetElem' X (I×J) Z] [GetElem' Y J Z]
    [OfFn X I Y] [LawfulOfFn X I]
    [IsGetElemCurry X I J]
    (f : I → Y) (ij : I×J) :
    (ofFn (coll:=X) f)[ij] = (f ij.1)[ij.2] := by
  rw[← getElem_uncurry]
  simp


----------------------------------------------------------------------------------------------------
-- Instances


-- Unit
instance : GetElem' α Unit α where
  getElem x _ _ := x

instance : InjectiveGetElem α Unit where
  getElem_injective := by intro x y h; have := congrFun h (); simp_all[getElem]

instance : OfFn α Unit α where
  ofFn f := f ()

instance : LawfulOfFn α Unit where
  getElem_ofFn := by intros; simp[getElem,ofFn]


-- Prod
instance [GetElem' α ι γ] [GetElem' β κ γ] :
    GetElem (α×β) (ι⊕κ) γ (fun _ _ => True) where
  getElem x i _ := match x, i with | (x,y), .inl i => x[i] | (x,y), .inr j => y[j]


instance [GetElem' α ι γ] [GetElem' β κ γ]
    [InjectiveGetElem α ι] [InjectiveGetElem β κ] :
    InjectiveGetElem (α×β) (ι⊕κ) where
  getElem_injective := by
    intro x y h
    cases x; cases y; simp
    constructor
    · apply getElem_injective (idx:=ι); funext i
      exact congrFun h (.inl i)
    · apply getElem_injective (idx:=κ); funext j
      exact congrFun h (.inr j)

instance [SetElem' α ι γ] [SetElem' β κ γ] :
    SetElem (α×β) (ι⊕κ) γ (fun _ _ => True) where
  setElem x i v _ :=
    match x, i with
    | (x,y), .inl i => (setElem x i v .intro,y)
    | (x,y), .inr j => (x, setElem y j v .intro)
  setElem_valid := by simp

instance [SetElem' α ι γ] [SetElem' β κ γ]
         [GetElem' α ι γ] [GetElem' β κ γ]
         [LawfulSetElem α ι] [LawfulSetElem β κ] :
    LawfulSetElem (α×β) (ι⊕κ) where
  getElem_setElem_eq := sorry_proof
  getElem_setElem_neq := sorry_proof


instance [OfFn α ι γ] [OfFn β κ γ] :
    OfFn (α×β) (ι⊕κ) γ where
  ofFn f := (ofFn (fun i => f (.inl i)), ofFn (fun j => f (.inr j)))

instance [GetElem' α ι γ] [GetElem' β κ γ]
    [OfFn α ι γ] [OfFn β κ γ] [LawfulOfFn α ι] [LawfulOfFn β κ] :
    LawfulOfFn (α×β) (ι⊕κ) where
  getElem_ofFn := by intro f i; cases i <;> simp[getElem,ofFn]

@[simp, simp_core]
theorem getElem_prod_inl [GetElem' α ι γ] [GetElem' β κ γ]
        (x : α) (y : β) (i : ι) : (x,y)[Sum.inl (β:=κ) i] = x[i] := by rfl

@[simp, simp_core]
theorem getElem_prod_inr [GetElem' α ι γ] [GetElem' β κ γ]
        (x : α) (y : β) (j : κ) : (x,y)[Sum.inr (α:=ι) j] = y[j] := by rfl


----------------------------------------------------------------------------------------------------
-- GetElem OfFn simproc ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

open Lean Meta Expr
/-- Simproc for zetaDelta reduction in very specific case:

Consider that we create and array and then immediatelly take an element of it.
```
let xs := ⊞ i => f i
xs[i]
```
we want this to reduce to `f i`. This simproc does that witout the need of turing on
 `zeta`/`zeteDelta` option of `simp`.

 -/
simproc_decl getElem_ofFn_zetaDelta (getElem _ _ _) := fun e => do
  if e.isAppOfArity' ``getElem 8 then
    let xs := e.getArg! 5
    if xs.isFVar then
      if let .some val ← xs.fvarId!.getValue? then
        if val.isAppOfArity ``ofFn 5 then
          let e' : Expr :=
            Expr.letE `xi (← inferType e) (e.setArg 5 val) (.bvar 0) false
          return .continue (.some { expr := e'})
  return .continue
