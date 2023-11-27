import Mathlib.Init.Function
import Mathlib.Algebra.Group.Basic
import SciLean.Util.SorryProof
import SciLean.Tactic.FTrans.Init

namespace SciLean

open Function

class StructType (X : Sort _) (I : (Sort _)) (XI : outParam <| I → Sort _) where
  structProj (x : X) (i : I) : (XI i)
  structMake (f : (i : I) → (XI i)) : X
  structModify (i : I) (f : XI i → XI i) (x : X) : X
  left_inv : LeftInverse structProj structMake
  right_inv : RightInverse structProj structMake
  structProj_structModify : ∀ i f x, 
    structProj (structModify i f x) i = f (structProj x i)
  structProj_structModify' : ∀ i j f x, 
    i ≠ j → structProj (structModify i f x) j = structProj x j

attribute [simp, ftrans_simp] StructType.structProj_structModify StructType.structProj_structModify'
export StructType (structProj structMake structModify)

def oneHot {X I XI} [StructType X I XI] [DecidableEq I] [∀ i, Zero (XI i)] (i : I) (xi : XI i) : X := 
  structMake fun i' =>
    if h : i=i' then
      h▸xi
    else
      0

namespace StructType

variable {X I XI} [StructType X I XI]

@[simp, ftrans_simp]
theorem structProj_structMake (f : (i : I) → XI i) (i : I)
  : structProj (X:=X) (structMake f) i = f i := by apply congr_fun; apply left_inv

@[simp, ftrans_simp]
theorem structMake_structProj (x : X)
  : structMake (X:=X) (fun (i : I) => structProj x i) = x := by apply right_inv

@[simp, ftrans_simp]
theorem structProj_oneHot [DecidableEq I] [∀ (i : I), Zero (XI i)] (xi : XI i)
  : structProj (oneHot (X:=X) i xi) i = xi := by simp[oneHot]

@[simp, ftrans_simp]
theorem structProj_oneHot' [DecidableEq I] [∀ (i : I), Zero (XI i)] (i j : I) (xi : XI i) (h : i≠j) 
  : structProj (oneHot (X:=X) i xi) j = 0 := 
by 
  simp[oneHot]
  if h':i=j then simp [h'] at h else simp[h']

theorem _root_.SciLean.structExt (x x' : X) : (∀ i : I, structProj x i = structProj x' i) → x = x' := 
by
  intro h; rw[← structMake_structProj (I:=I) x]; rw[← structMake_structProj (I:=I) x']; simp[h]


--------------------------------------------------------------------------------
-- Basic instances -------------------------------------------------------------
--------------------------------------------------------------------------------


-- Every type ------------------------------------------------------------------
--------------------------------------------------------------------------------

/-- Every type is `StructType` with `Unit` as index set.

The motivation behind this instance is that type like `X×(Y×Z)` should have `StructType`
instance that the type has three components. Such instance is defines inductively 
and this is the base case of this induction, the inductive step is `instStrucTypeProd`.
-/
instance (priority:=low) instStructTypeDefault : StructType α Unit (fun _ => α) where
  structProj := fun x _ => x
  structMake := fun f => f ()
  structModify := fun _ f x => f x
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by simp

-- Pi --------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low+1) instStrucTypePi
  (I : Type _) (E : I → Type _)
  (J : I → Type _) (EJ : (i : I) → (J i) → Type _)
  [∀ (i : I), StructType (E i) (J i) (EJ i)] [DecidableEq I]
  : StructType (∀ i, E i) ((i : I) × (J i)) (fun ⟨i,j⟩ => EJ i j) where
  structProj := fun f ⟨i,j⟩ => StructType.structProj (f i) j
  structMake := fun f i => StructType.structMake fun j => f ⟨i,j⟩
  structModify := fun ⟨i,j⟩ f x i' => 
    if h : i'=i then
      StructType.structModify (I:=J i') (h▸j) (h▸f) (x i')
    else
      (x i')
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by 
    intro ⟨i,j⟩ ⟨i',j'⟩; intros _ _ H; simp
    if h: i' = i then
      subst h
      if h': j=j' then
        simp[h'] at H
      else
        simp[structProj_structModify' _ _ _ _ h']
    else 
      simp[h]


instance instStrucTypeArrow
  (E I J : Type _) (EI : I → Type _)
  [StructType E I EI] [DecidableEq J]
  : StructType (J → E) (J×I) (fun (j,i) => EI i) where
  structProj := fun f (j,i) => StructType.structProj (f j) i
  structMake := fun f j => StructType.structMake fun i => f (j,i)
  structModify := fun (j,i) f x j' =>   
    if j=j' then
      StructType.structModify i f (x j)
    else
      (x j')
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by 
    intro (j,i) (j',i') f x H; simp
    if h: j = j' then
      subst h
      if h': i=i' then
        simp[h'] at H
      else
        simp[h']
    else 
      simp[h]


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

abbrev _root_.Prod.TypeFun {I J: Type _} (EI : I → Type _) (FJ : J → Type _) (i : Sum I J) : Type _ :=
  match i with
  | .inl a => EI a
  | .inr b => FJ b

instance instStrucTypeProd [StructType E I EI] [StructType F J FJ] 
  : StructType (E×F) (Sum I J) (Prod.TypeFun EI FJ) where
  structProj := fun (x,y) i =>
    match i with
    | .inl a => StructType.structProj x a
    | .inr b => StructType.structProj y b
  structMake := fun f => (StructType.structMake (fun a => f (.inl a)), 
                    StructType.structMake (fun b => f (.inr b)))
  structModify := fun i f (x,y) =>
    match i with
    | .inl a => (StructType.structModify a f x, y)
    | .inr b => (x, StructType.structModify b f y)
  left_inv := by intro x; funext i; induction i <;> simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by intro i j f x h; induction j <;> induction i <;> (simp at h; simp (disch:=assumption))



  

