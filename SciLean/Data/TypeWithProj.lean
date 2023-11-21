import Mathlib.Init.Function
import SciLean.Util.SorryProof

namespace SciLean

open Function

class TypeWithProj (F : Sort _) (I : outParam (Sort _)) (E : outParam <| I → Sort _) where
  proj : F → (i : I) → (E i)
  intro : ((i : I) → (E i)) → F
  modify : (i : I) → (E i → E i) → (F → F)
  left_inv : LeftInverse proj intro
  right_inv : RightInverse proj intro
  -- TODO: theorem about modify


--------------------------------------------------------------------------------
-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

abbrev _root_.Prod.TypeFun {αIdx βIdx : Type _} (αType : αIdx → Type _) (βType : βIdx → Type _) (i : Sum αIdx βIdx) : Type _ :=
  match i with
  | .inl a => αType a
  | .inr b => βType b

instance (priority:=low) : TypeWithProj α Unit (fun _ => α) where
  proj := fun x _ => x
  intro := fun f => f ()
  modify := fun _ f x => f x
  left_inv := sorry_proof
  right_inv := sorry_proof

instance [TypeWithProj α αIdx αType] [TypeWithProj β βIdx βType] 
  : TypeWithProj (α×β) (Sum αIdx βIdx) (Prod.TypeFun αType βType) where
  proj := fun (x,y) i =>
    match i with
    | .inl a => TypeWithProj.proj x a
    | .inr b => TypeWithProj.proj y b
  intro := fun f => (TypeWithProj.intro (fun a => f (.inl a)), 
                     TypeWithProj.intro (fun b => f (.inr b)))
  modify := fun i f (x,y) =>
    match i with
    | .inl a => (TypeWithProj.modify a f x, y)
    | .inr b => (x, TypeWithProj.modify b f y)
  left_inv := sorry_proof
  right_inv := sorry_proof
