import Mathlib.Logic.Equiv.Basic

import SciLean.Tactic.FunTrans.Attr
import SciLean.Tactic.FunTrans.Elab

import SciLean.Meta.SimpAttr

open Lean

namespace SciLean

/-- Type `α` is isomorphic to `α'`.

Think about this class such that for each `tag` we get partial function `Type → Type`.
-/
class IsomorphicType (tag : Name) (α : Sort _) (α' : outParam (Sort _)) where
  equiv : α ≃ α'

variable {α β γ : Type _}
  {α' β' γ' : outParam (Type _)}
  (tag : Name)
  [IsomorphicType tag α α']
  [IsomorphicType tag β β']
  [IsomorphicType tag γ γ']

@[fun_trans]
def isomorph (f : α → β) (a' : α') : β' :=
    a' |> (IsomorphicType.equiv tag (α:=α)).symm
       |> f
       |> (IsomorphicType.equiv tag)

def invIsomorph (f : α' → β') (a : α) : β :=
    a |> (IsomorphicType.equiv tag (α:=α))
      |> f
      |> (IsomorphicType.equiv tag).symm

@[simp, simp_core]
theorem isomorph.app (f : α → β) (x : α)
  : (IsomorphicType.equiv tag) (f x) = isomorph tag f (IsomorphicType.equiv tag x) :=
by
  simp[IsomorphicType.equiv, isomorph]

theorem isomorph.ext (a b : α)
  : (IsomorphicType.equiv tag a) = (IsomorphicType.equiv tag b) → a = b :=
by
  simp[IsomorphicType.equiv]

theorem isomorph.funext {β β' : Sort _} [IsomorphicType tag β β'] (f g : α → β)
  : isomorph tag f = isomorph tag g → f = g :=
by
  intro h; funext _; apply ext tag; simp[app tag,h]

instance : IsomorphicType tag (α × β) (α' × β') where
  equiv := {
    toFun := fun (x,y) =>
      (IsomorphicType.equiv tag x, IsomorphicType.equiv tag y)
    invFun := fun (x,y) =>
      ((IsomorphicType.equiv tag).symm x, (IsomorphicType.equiv tag).symm y)
    left_inv := by simp[Function.LeftInverse, IsomorphicType.equiv]
    right_inv := by simp[Function.LeftInverse, Function.RightInverse, IsomorphicType.equiv]
  }

instance : IsomorphicType tag (α → β) (α' → β') where
  equiv := {
    toFun := fun f => isomorph tag f
    invFun := fun f => invIsomorph tag f
    left_inv := by intro f; funext x; simp [-isomorph.app, IsomorphicType.equiv, isomorph, invIsomorph]
    right_inv := by intro f; funext x; simp[IsomorphicType.equiv, isomorph, invIsomorph]
  }

instance (P : Prop) : IsomorphicType tag P P where
  equiv := {
    toFun := fun p => p
    invFun := fun p => p
    left_inv := by simp[Function.LeftInverse]
    right_inv := by simp[Function.RightInverse,Function.LeftInverse]
  }
