import Mathlib.Algebra.Group.Basic
import SciLean.Util.SorryProof
import SciLean.Meta.SimpAttr
import SciLean.Data.Function

namespace SciLean

open Function

/-- `StructType X I XI` says that the type `X` behaves like a structure with fields indexed by
`i : I` of type `XI i`. -/
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

attribute [simp, simp_core] StructType.structProj_structModify StructType.structProj_structModify'
export StructType (structProj structMake structModify)
attribute [simp, simp_core] structProj structMake structModify

def oneHot {X I XI} [StructType X I XI] [DecidableEq I] [∀ i, Zero (XI i)] (i : I) (xi : XI i) : X :=
  structMake fun i' =>
    if h : i=i' then
      h▸xi
    else
      0

namespace StructType

variable {X I XI} [StructType X I XI]

@[simp, simp_core]
theorem structProj_structModify'' (x : X) (i j : I) (f : XI i → XI i) (h : i = j) :
    structProj (structModify i f x) j = h ▸ f (structProj x i) := by
  subst h; simp only [structProj_structModify]

@[simp, simp_core]
theorem structProj_structMake (f : (i : I) → XI i) (i : I)
  : structProj (X:=X) (structMake f) i = f i := by apply congr_fun; apply left_inv

@[simp, simp_core]
theorem structMake_structProj (x : X)
  : structMake (X:=X) (fun (i : I) => structProj x i) = x := by apply right_inv

@[simp, simp_core]
theorem structProj_oneHot [DecidableEq I] [∀ (i : I), Zero (XI i)] (xi : XI i)
  : structProj (oneHot (X:=X) i xi) i = xi := by simp[oneHot]

@[simp, simp_core]
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

@[simp, simp_core]
theorem oneHot_unit {X} [Zero X] (x : X)
  : oneHot (X:=X) (I:=Unit) () x = x := by rfl

@[simp, simp_core]
theorem structProj_unit (x : E)
  : structProj (I:=Unit) x ()
    =
    x := rfl

@[simp, simp_core]
theorem structMake_unit (f : Unit → E)
  : structMake (I:=Unit) f
    =
    f () := rfl

@[simp, simp_core]
theorem structModify_unit (f : E → E) (x : E)
  : structModify (I:=Unit) () f x
    =
    f x := rfl


-- Pi --------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low+1) instStrucTypePiSimple
  (I : Type _) (E : I → Type _) [DecidableEq I]
  : StructType (∀ i, E i) I E where
  structProj := fun f i => f i
  structMake := fun f i => f i
  structModify := fun i g f => Function.modify f i g
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by
    intro i i'; intros _ _ H
    if h: i' = i then
      simp [h] at H
    else
      simp[h]

set_option linter.unusedVariables false in
instance (priority:=low+1) instStrucTypePi
  (I : Type _) (E : I → Type _)
  (J : I → Type _) (EJ : (i : I) → (J i) → Type _)
  [∀ (i : I), StructType (E i) (J i) (EJ i)] [DecidableEq I]
  : StructType (∀ i, E i) ((i : I) × (J i)) (fun ij => EJ ij.1 ij.2) where
  structProj := fun f ⟨i,j⟩ => StructType.structProj (f i) j
  structMake := fun f i => StructType.structMake fun j => f ⟨i,j⟩
  structModify := fun ⟨i,j⟩ f x => Function.modify x i (StructType.structModify (I:=J i) j f)
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

instance instStrucTypeArrowSimple
  (E J : Type _) [DecidableEq J]
  : StructType (J → E) J (fun _ => E) where
  structProj := fun f j => f j
  structMake := fun f j => f j
  structModify := fun j g f => Function.modify f j g
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by
    intro j j' f x H
    if h: j' = j then
      simp [h] at H
    else
      simp[h]

instance instStrucTypeArrow
  (E I J : Type _) (EI : I → Type _)
  [StructType E I EI] [DecidableEq J]
  : StructType (J → E) (J×I) (fun ji => EI ji.2) where
  structProj := fun f (j,i) => StructType.structProj (f j) i
  structMake := fun f j => StructType.structMake fun i => f (j,i)
  structModify := fun (j,i) f x => Function.modify x j (StructType.structModify i f)
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by
    intro (j,i) (j',i') f x H; simp
    if h: j'=j then
      subst h
      if h': i=i' then
        simp[h'] at H
      else
        simp[h']
    else
      simp[h]


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance instStrucTypeProd
  [StructType E I EI] [StructType F J FJ]
  : StructType (E×F) (Sum I J) (Sum.rec EI FJ) where
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
  structProj_structModify' := by
    intro i j f x h
    induction j <;> induction i <;> (simp at h; simp (disch:=assumption))


instance instStrucTypeSigma
  [StructType E I EI] [StructType F J FJ]
  : StructType ((_:E)×F) (Sum I J) (Sum.rec EI FJ) where
  structProj := fun ⟨x,y⟩ i =>
    match i with
    | .inl a => structProj x a
    | .inr b => structProj y b
  structMake := fun f =>
    ⟨structMake (fun a => f (.inl a)),
     structMake (fun b => f (.inr b))⟩
  structModify := fun i f ⟨x,y⟩ =>
    match i with
    | .inl a => ⟨structModify a f x, y⟩
    | .inr b => ⟨x, structModify b f y⟩
  left_inv := by intro x; funext i; induction i <;> simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  structProj_structModify := by simp
  structProj_structModify' := by
    intro i j f x h
    induction j <;> induction i <;> (simp at h; simp (disch:=assumption))


-- @[simp, simp_core]
-- theorem structMake_sum_match [StructType E I EI] [StructType F J FJ] (f : (i : I) → EI i) (g : (j : J) → FJ j)
--   : structMake (X:=E×F) (I:=I⊕J) (fun | .inl i => f i | .inr j => g j)
--     =
--     (structMake (X:=E) f, structMake (X:=F) g) :=
-- by
--   simp[structMake]

@[simp low, simp_core low]
theorem structModify_inl [StructType E I EI] [StructType F J FJ] (i : I) (f : EI i → EI i) (xy : E×F)
  : structModify (I:=I⊕J) (.inl i) f xy
    =
    {xy with fst := structModify i f xy.1} :=
by
  conv =>
    lhs
    simp[structModify]

-- @[simp, simp_core]
-- theorem structModify_inl' [StructType E I EI] [StructType F J FJ] (i : I) (f : EI i → EI i) (x : E) (y : F)
--   : structModify (I:=I⊕J) (.inl i) f (x, y)
--     =
--     (structModify i f x, y) :=
-- by
--   conv =>
--     lhs
--     simp[structModify]

@[simp low, simp_core low]
theorem structModify_inr [StructType E I EI] [StructType F J FJ] (j : J) (f : FJ j → FJ j) (xy : E×F)
  : structModify (I:=I⊕J) (.inr j) f xy
    =
    (xy.1, structModify j f xy.2) :=
by
  simp[structModify]

-- @[simp, simp_core]
-- theorem structModify_inr' [StructType E I EI] [StructType F J FJ] (j : J) (f : FJ j → FJ j) (x : E) (y : F)
--   : structModify (I:=I⊕J) (.inr j) f (x, y)
--     =
--     (x, structModify j f y) :=
-- by
--   simp[structModify]
