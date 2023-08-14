-- import SciLean.Core.Attributes
import SciLean.Prelude
import SciLean.Core.Vec
import SciLean.Data.Prod

import SciLean.Core.Tactic.FunctionTransformation.Init

import Mathlib.Data.FunLike.Basic

namespace SciLean

open Function

@[fun_prop_def]
structure IsInv {X Y : Type _} (f : X → Y) : Prop where
  isInv : Bijective f

structure InvMap (X Y : Type _) where
  toFun : X → Y 
  isInv_toFun : IsInv toFun := by infer_instance

/-- `X <-> Y` is the space of all invertible maps between `X` and `Y`.

The notation `X ↔ Y` is prefered, but this fixes pure ASCII equivalent. -/
infixr:25 " <-> " => InvMap 

/-- `X ↔ Y` is the space of all invertible maps between `X` and `Y`. 

Can be also written as `X <-> Y` -/
infixr:25 " ↔ " => InvMap

-- Lambda notation
open Lean.TSyntax.Compat in
macro "λ"   xs:Lean.explicitBinders " ↔ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.InvMap.mk xs b
open Lean.TSyntax.Compat in
macro "fun"   xs:Lean.explicitBinders " ↔ " b:term : term =>
  Lean.expandExplicitBinders `SciLean.InvMap.mk xs b


class InvMapClass (F : Type _) (X Y : outParam <| Type _)
  extends FunLike F X fun _ => Y where
  map_isInv (f : F) : IsInv f


export InvMapClass (map_isInv)

attribute [fun_prop] map_isInv

section InvMapClass

  variable {F X Y : Type _} [InvMapClass F X Y]

  instance : CoeTC F (X ↔ Y) :=
    ⟨fun f =>
      { toFun := f
        isInv_toFun := map_isInv f }⟩

end InvMapClass

namespace InvMap

  -- The following is heavily inspired by ContinuousMap

  variable {X Y Z W : Type _} 

  instance : InvMapClass (X↔Y) X Y where
    map_isInv f := f.isInv_toFun
    coe f := f.toFun
    coe_injective' := sorry_proof
    
  @[simp]
  theorem toFun_eq_coe {f : X ↔ Y} : f.toFun = (f : X → Y) :=
    rfl

  def Simps.apply (f : X ↔ Y) : X → Y := f

  initialize_simps_projections InvMap (toFun → apply)

  @[simp]
  protected theorem coe_coe {F : Type} [InvMapClass F X Y] (f : F) : ⇑(f : X ↔ Y) = f :=
    rfl

  @[ext]
  theorem ext {f g : X ↔ Y} (h : ∀ x, f x = g x) : f = g :=
    FunLike.ext _ _ h

  @[fun_prop]
  theorem isInv_set_coe (s : Set (X↔Y)) (f : s) : IsInv (f : X → Y) :=
    map_isInv f.1

  @[simp]
  theorem coe_mk (f : X → Y) (h : IsInv f) : ⇑(⟨f, h⟩ : X ↔ Y) = f :=
    rfl

  @[simp]
  theorem eta (f : X ↔ Y)
      : (λ (x : X) ↔ f x) = f := by rfl; done

  protected def id : X ↔ X :=
    InvMap.mk (λ x => x) sorry

  @[simp]
  theorem coe_id : ⇑(InvMap.id : X ↔ X) = _root_.id := 
    rfl

  @[simp]
  theorem id_apply (x : X) : InvMap.id x = x :=
    rfl

  ------------------------------------------------------------------------------
  -- Basic combinators like const, comp, curry, uncurry, prodMk, prodMap, pi
  ------------------------------------------------------------------------------
  
  -- comp --
  ----------
  def comp : (Y↔Z)↔(X↔Y)↔X↔Z := 
    InvMap.mk (λ f : Y↔Z => 
      InvMap.mk (λ g : X↔Y => 
        InvMap.mk (λ x : X => f (g x)) 
        sorry)
      sorry)
    sorry

  @[simp]
  theorem coe_comp (f : Y ↔ Z) (g : X ↔ Y) : ⇑(comp f g) = f ∘ g := 
    rfl

  @[simp] 
  theorem comp_apply (f : Y ↔ Z) (g : X ↔ Y) (x : X) : comp f g x = f (g x) :=
    rfl

  @[simp] 
  theorem comp_assoc (f : Y ↔ Z) (g : X ↔ Y) (h : W ↔ X) : 
      comp (comp f g) h = comp f (comp g h) :=
    rfl

