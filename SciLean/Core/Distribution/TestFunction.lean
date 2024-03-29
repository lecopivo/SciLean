import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Decomposition.Lebesgue

import SciLean.Core.FunctionPropositions
import SciLean.Util.SorryProof

open MeasureTheory ENNReal

namespace SciLean

local notation "∞" => (⊤ : ℕ∞)

-- variable
--   {R} [RealScalar R]
--   {W} [Vec R W] [Module ℝ W]
--   {X}


-- TODO: Move somewhere
class TCOr (A B : Sort _) where
  val : PSum A B

set_option checkBinderAnnotations false in
instance {A B} [inst : A] : TCOr A B where
  val := .inl inst

set_option checkBinderAnnotations false in
instance {A B} [inst : B] : TCOr A B where
  val := .inr inst


structure IsTestFunction
    {R : Type u} [RealScalar R]
    {X : Type v} [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)]
    (f : X → R) : Prop where
  is_smooth :
    match space.val with
    | .inl _ => ContCDiff R ∞ f
    | .inr _ => True
  has_compact_support : HasCompactSupport f

structure TestFunctionSpace (R : Type u) [RealScalar R] (X : Type v)
    [TopologicalSpace X] [space : TCOr (Vec R X) (DiscreteTopology X)] where
  toFun : X → R
  is_test_fun : IsTestFunction toFun

notation "𝒟" X => TestFunctionSpace defaultScalar% X

@[app_unexpander TestFunctionSpace] def unexpandTestFunctionSpace : Lean.PrettyPrinter.Unexpander
  | `($(_) $_ $X) => `(𝒟 $X)
  | _ => throw ()

variable
  {R} [RealScalar R]
  [TopologicalSpace X]
  [space : TCOr (Vec R X) (DiscreteTopology X)] -- here we are getting topology in `Vec R X` for the second time :( this will cause issues ...

set_default_scalar R

instance : FunLike (𝒟 X) X R where
  coe f x := f.toFun x
  coe_injective' := sorry_proof

instance : Add (𝒟 X) := ⟨fun f g : 𝒟 X => ⟨fun x => f x + g x, sorry_proof⟩⟩
instance : Sub (𝒟 X) := ⟨fun f g : 𝒟 X => ⟨fun x => f x - g x, sorry_proof⟩⟩
instance : SMul R (𝒟 X) := ⟨fun r f => ⟨fun x => r * f x, sorry_proof⟩⟩
instance : Neg (𝒟 X) := ⟨fun f => ⟨fun x => - f x, sorry_proof⟩⟩
instance : Zero (𝒟 X) := ⟨⟨fun x => - 0, sorry_proof⟩⟩

instance : UniformSpace (𝒟 X) := sorry
instance : Vec R (𝒟 X) := Vec.mkSorryProofs


----------------------------------------------------------------------------------------------------
-- Test function approximation ---------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Restrict function `f` by a ball of radius `n` and do smooth by convolution with radius `1/n`.

If `X` is discrete space then we do not need to do smoothing. -/
opaque testFunApprox (n : ℕ) (f : X → R) : 𝒟 X


----------------------------------------------------------------------------------------------------
-- Properties --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem TestFunctionSpace.eval_CDifferentiable (x : X) :
    CDifferentiable R (fun φ : 𝒟 X => φ x) := sorry_proof

@[fun_prop]
theorem TestFunctionSpace.eval_IsLinearMap (x : X) :
    IsLinearMap R (fun φ : 𝒟 X => φ x) := sorry_proof

@[fun_prop]
theorem TestFunctionSpace.eval_IsSmoothLinearMap (x : X) :
    IsSmoothLinearMap R (fun φ : 𝒟 X => φ x) := by constructor <;> fun_prop


variable
  {W} [Vec R W]
  {X} [Vec R X]

-- @[fun_prop]
-- theorem TestFunctionSpace.eval_CDifferentiable_rule :
--     CDifferentiable R (fun (φx : (𝒟 X)×X) => φx.1 φx.2) := sorry_proof


@[fun_prop]
theorem TestFunctionSpace.eval_CDifferentiableAt_rule (w : W)
    (φ : W → 𝒟 X) (x : W → X)
    (hφ : CDifferentiableAt R φ w) (hx : CDifferentiableAt R x w) :
    CDifferentiableAt R (fun w : W => (φ w) (x w)) w := sorry_proof


@[fun_prop]
theorem TestFunctionSpace.eval_CDifferentiable_rule'
    (φ : W → 𝒟 X) (x : W → X)
    (hφ : CDifferentiable R φ) (hx : CDifferentiable R x) :
    CDifferentiable R (fun w : W => (φ w) (x w)) := by intro w; fun_prop
