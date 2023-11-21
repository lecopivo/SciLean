import Mathlib.Init.Function
import Mathlib.Algebra.Group.Basic
import SciLean.Util.SorryProof

namespace SciLean

open Function

class StructLike (E : Sort _) (I : outParam (Sort _)) (EI : outParam <| I → Sort _) where
  proj : E → (i : I) → (EI i)
  make : ((i : I) → (EI i)) → E
  modify : (i : I) → (EI i → EI i) → (E → E)
  left_inv : LeftInverse proj intro
  right_inv : RightInverse proj intro
  -- TODO: theorem about modify


/-- Every type is `StructLike` with `Unit` as index set.
-/
instance (priority:=low) : StructLike α Unit (fun _ => α) where
  proj := fun x _ => x
  make := fun f => f ()
  modify := fun _ f x => f x
  left_inv := sorry_proof
  right_inv := sorry_proof

--------------------------------------------------------------------------------
-- Pi --------------------------------------------------------------------------
--------------------------------------------------------------------------------

instance (priority:=low) 
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
  left_inv := sorry_proof
  right_inv := sorry_proof

instance
  (E I J : Type _) (EI : I → Type _)
  [StructLike E I EI] [DecidableEq J]
  : StructLike (J → E) (J×I) (fun (j,i) => EI i) where
  proj := fun f (j,i) => StructLike.proj (f j) i
  make := fun f j => StructLike.make fun i => f (j,i)
  modify := fun (j,i) f x j' =>   
    if h : j=j' then
      StructLike.modify i f (x j)
    else
      (x j')
      
  left_inv := sorry_proof
  right_inv := sorry_proof


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
  left_inv := sorry_proof
  right_inv := sorry_proof



--------------------------------------------------------------------------------
-- TODO: Add some lawfulness w.r.t. to +,•,0

@[simp]
theorem StruckLike.make_zero
  {X I : Type}  {XI : I → Type} [StructLike X I XI] 
  [Zero X] [∀ i, Zero (XI i)]
  : StructLike.make (E:=X) (fun _ => 0)
    =
    0 :=
by
  sorry


@[simp]
theorem StruckLike.make_add
  {X I : Type}  {XI : I → Type} [StructLike X I XI] 
  [Zero X] [∀ i, Zero (XI i)]
  : StructLike.make (E:=X) (fun _ => 0)
    =
    0 :=
by
  sorry
