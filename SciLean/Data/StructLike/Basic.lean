import Mathlib.Init.Function
import Mathlib.Algebra.Group.Basic
import SciLean.Util.SorryProof

namespace SciLean

open Function

class StructLike (X : Sort _) (I : outParam (Sort _)) (XI : outParam <| I → Sort _) where
  proj (x : X) (i : I) : (XI i)
  make (f : (i : I) → (XI i)) : X
  modify (i : I) (f : XI i → XI i) (x : X) : X
  left_inv : LeftInverse proj make
  right_inv : RightInverse proj make
  proj_modify : ∀ i f x, 
    proj (modify i f x) i = f (proj x i)
  proj_modify' : ∀ i j f x, 
    i ≠ j → proj (modify i f x) j = proj x j

namespace StructLike

variable {X I XI} [StructLike X I XI]

attribute [simp] proj_modify proj_modify'

@[simp]
theorem proj_make (f : (i : I) → XI i) (i : I)
  : proj (X:=X) (make f) i = f i := by apply congr_fun; apply left_inv

@[simp]
theorem make_proj (x : X)
  : make (X:=X) (fun i => proj x i) = x := by apply right_inv

def oneHot [DecidableEq I] [∀ i, Zero (XI i)] (i : I) (xi : XI i) : X := 
  StructLike.make fun i' =>
    if h : i=i' then
      h▸xi
    else
      0

theorem ext (x x' : X) : (∀ i, proj x i = proj x' i) → x = x' := 
by
  intro h; rw[← make_proj x]; rw[← make_proj x']; simp[h]


/-- Every type is `StructLike` with `Unit` as index set.
-/
instance (priority:=low) instStructLikeDefault : StructLike α Unit (fun _ => α) where
  proj := fun x _ => x
  make := fun f => f ()
  modify := fun _ f x => f x
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  proj_modify := by simp
  proj_modify' := by simp

--------------------------------------------------------------------------------
-- Pi --------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low+1) 
  (I : Type _) (E : I → Type _)
  (J : I → Type _) (EJ : (i : I) → (J i) → Type _)
  [∀ (i : I), StructLike (E i) (J i) (EJ i)] [DecidableEq I]
  : StructLike (∀ i, E i) ((i : I) × (J i)) (fun ⟨i,j⟩ => EJ i j) where
  proj := fun f ⟨i,j⟩ => StructLike.proj (f i) j
  make := fun f i => StructLike.make fun j => f ⟨i,j⟩
  modify := fun ⟨i,j⟩ f x i' => 
    if h : i'=i then
      StructLike.modify (h▸j) (h▸f) (x i')
    else
      (x i')
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  proj_modify := by simp
  proj_modify' := by 
    intro ⟨i,j⟩ ⟨i',j'⟩; intros _ _ H; simp
    if h: i' = i then
      subst h
      if h': j=j' then
        simp[h'] at H
      else
        simp[proj_modify' _ _ _ _ h']
    else 
      simp[h]


instance
  (E I J : Type _) (EI : I → Type _)
  [StructLike E I EI] [DecidableEq J]
  : StructLike (J → E) (J×I) (fun (j,i) => EI i) where
  proj := fun f (j,i) => StructLike.proj (f j) i
  make := fun f j => StructLike.make fun i => f (j,i)
  modify := fun (j,i) f x j' =>   
    if j=j' then
      StructLike.modify i f (x j)
    else
      (x j')
  left_inv := by simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  proj_modify := by simp
  proj_modify' := by 
    intro (j,i) (j',i') f x H; simp
    if h: j = j' then
      subst h
      if h': i=i' then
        simp[h'] at H
      else
        simp[h']
    else 
      simp[h]


--------------------------------------------------------------------------------
-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

abbrev _root_.Prod.TypeFun {I J: Type _} (EI : I → Type _) (FJ : J → Type _) (i : Sum I J) : Type _ :=
  match i with
  | .inl a => EI a
  | .inr b => FJ b

instance [StructLike E I EI] [StructLike F J FJ] 
  : StructLike (E×F) (Sum I J) (Prod.TypeFun EI FJ) where
  proj := fun (x,y) i =>
    match i with
    | .inl a => StructLike.proj x a
    | .inr b => StructLike.proj y b
  make := fun f => (StructLike.make (fun a => f (.inl a)), 
                    StructLike.make (fun b => f (.inr b)))
  modify := fun i f (x,y) =>
    match i with
    | .inl a => (StructLike.modify a f x, y)
    | .inr b => (x, StructLike.modify b f y)
  left_inv := by intro x; funext i; induction i <;> simp[LeftInverse]
  right_inv := by simp[Function.RightInverse, LeftInverse]
  proj_modify := by simp
  proj_modify' := by intro i j f x h; induction j <;> induction i <;> (simp at h; simp (disch:=assumption))



  

