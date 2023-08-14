import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Module.Prod

-- TODO: minimize this import, simp and aesop fail without it at some places
import Mathlib.Analysis.Calculus.FDeriv.Basic

import SciLean.Util.Profile

namespace SciLean

/-- 
`BroadcastType tag R ι X MX` says that `MX` is `ι`-many copies of `X`. This is used for broadcasting/vectorization of code.

For example:

`BroadcastType Prod ℝ (Fin 3) X (X×X×X)`
`BroadcastType NArray ℝ (Fin n) X (NArray X n)`

Arguments
1. `tag` - is used to indicate the class of broadcasting types. For example, dense or sparse matrices are broadcast type for vectors. 
2. `R` - over which field/ring we do this broadcasting. We require that `MX` is `R`-linear isomorphic to `ι → X`. Right now, it is not entirelly clear what is the role of this argument, but we need it to state the linear isomorphism.
3. `ι` - index set specifying how many copies of `X` we are making
4. `X` - type to broadcast/vectorize
  -/
class BroadcastType (tag : Lean.Name) (R : Type _) [Ring R] (ι : Type _) (X : Type _) [AddCommGroup X] [Module R X] (MX : outParam $ Type _) [outParam $ AddCommGroup MX] [outParam $ Module R MX] where
  equiv  : MX ≃ₗ[R] (ι → X)


variable 
  {R : Type _} [Ring R]
  {X : Type _} [AddCommGroup X] [Module R X]
  {Y : Type _} [AddCommGroup Y] [Module R Y]
  {MX : outParam $ Type _} [outParam $ AddCommGroup MX] [outParam $ Module R MX]
  {MY : outParam $ Type _} [outParam $ AddCommGroup MY] [outParam $ Module R MY]
  {ι : Type _} -- [Fintype ι]
  {κ : Type _} -- [Fintype κ]
  {E ME : κ → Type _} 
  [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, AddCommGroup (ME j)] [∀ j, Module R (ME j)]

 
open BroadcastType in
instance [BroadcastType tag R ι X MX] [BroadcastType tag R ι Y MY] : BroadcastType tag R ι (X×Y) (MX×MY) where
  equiv := {
    toFun  := fun (mx,my) i => (equiv tag (R:=R) mx i, 
                                equiv tag (R:=R) my i)
    invFun := fun xy => ((equiv tag (R:=R)).invFun fun i => (xy i).1, 
                         (equiv tag (R:=R)).invFun fun i => (xy i).2) 
    map_add'  := by intro x y; funext i; simp
    map_smul' := by intro x y; funext i; simp
    left_inv  := fun _ => by simp
    right_inv := fun _ => by simp
  }

open BroadcastType in
instance [∀ j, BroadcastType tag R ι (E j) (ME j)]
  : BroadcastType tag R ι (∀ j, E j) (∀ j, ME j) where
  equiv := {
    toFun  := fun mx i j => equiv tag (R:=R) (mx j) i 
    invFun := fun x j => (equiv tag (R:=R)).invFun (fun i => x i j)
    map_add'  := by intro x y; funext i j; simp
    map_smul' := by intro x y; funext i j; simp
    left_inv  := fun _ => by simp
    right_inv := fun _ => by simp
  }


open BroadcastType in
instance : BroadcastType `Prod R (Fin 1) X X where
  equiv := {
    toFun  := fun x _ => x
    invFun := fun x => x 0
    map_add'  := by intro x y; funext _; simp
    map_smul' := by intro x y; funext _; simp
    left_inv  := fun _ => by rfl
    right_inv := fun _ => by funext i; rw[show i = 0 by aesop]
  }


open BroadcastType in
instance [BroadcastType `Prod R (Fin n) X MX] : BroadcastType `Prod R (Fin (n+1)) X (X×MX) where
  equiv := {
    toFun  := fun (x,mx) i =>
      match i with
      | ⟨0, _⟩ => x
      | ⟨i'+1, h⟩ => 
        let i' : Fin n := ⟨i', by aesop⟩
        equiv `Prod (R:=R) mx i'
    invFun := fun x => (x 0, (equiv `Prod (R:=R)).invFun fun i : Fin n => x ⟨i.1+1, by aesop⟩)
    map_add'  := by intro x y; funext ⟨i,hi⟩; induction i; simp; rfl; simp
    map_smul' := by intro x y; funext ⟨i,hi⟩; induction i; simp; rfl; simp
    left_inv  := fun (x,mx) => by simp; rfl
    right_inv := fun _ => by simp; funext ⟨i,hi⟩; induction i; simp; rfl
  }
