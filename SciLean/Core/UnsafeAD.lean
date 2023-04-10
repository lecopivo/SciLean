import SciLean.Core.CoreFunctions

namespace SciLean

class UnsafeAD where
  kaboom : False

macro "unsafe_ad" : tactic => `(tactic| have unsafe_ad : UnsafeAD := sorry)
macro "unsafe_ad" : conv => `(conv| tactic => unsafe_ad)

instance [inst : UnsafeAD] {X Y} [Vec X] [Vec Y] (f : X → Y) : IsSmooth f := inst.kaboom.elim
instance [inst : UnsafeAD] {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjDiff f := inst.kaboom.elim


function_properties HDiv.hDiv [UnsafeAD] (x y : ℝ) 
argument (x,y)
  IsSmooth := sorry,
  abbrev ∂ := λ dx dy => (dx*y - x*dy) / (y^2)  by sorry,
  abbrev 𝒯 := λ dx dy => let iy := 1/y; (x*iy, (dx*y - x*dy)*iy^2)  by sorry,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dxy' => let s := dxy' / (y^2); (s * y, - s * x) by sorry,
  abbrev ℛ := let iy := 1/y; (x*iy, λ dxy' => let s := dxy' * iy^2; (s * y, - s * x)) by sorry


function_properties SciLean.Inner.norm [UnsafeAD] {X} [Hilbert X] (x : X) 
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => ⟪dx, x⟫/‖x‖ by sorry,
  abbrev 𝒯 := λ dx => let xNorm := ‖x‖; (xNorm, ⟪dx, x⟫/xNorm) by sorry,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dx' => (dx'/‖x‖) • x by sorry,
  abbrev ℛ := let xNorm := ‖x‖; (xNorm, λ dx' => (dx'/‖x‖) • x) by sorry


function_properties SciLean.Real.sqrt [UnsafeAD] (x : ℝ) 
argument x
  IsSmooth := sorry,
  abbrev ∂ := λ dx => dx/(2 * x.sqrt) by sorry,
  abbrev 𝒯 := λ dx => let xNorm := ‖x‖; (xNorm, ⟪dx, x⟫/xNorm) by sorry,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dx' => (dx'/‖x‖) • x by sorry,
  abbrev ℛ := let xNorm := ‖x‖; (xNorm, λ dx' => (dx'/‖x‖) • x) by sorry


function_properties SciLean.Real.pow [UnsafeAD] (x y : ℝ) 
argument (x,y)
  IsSmooth := sorry,
  abbrev ∂ := λ dx dy => (dy * x.log + dx*y/x)*(x.pow y) by sorry,
  abbrev 𝒯 := λ dx dy => let xy := x.pow y; (xy, (dy * x.log + dx*y/x)*xy) by sorry,
  HasAdjDiff := sorry,
  abbrev ∂† := λ dxy' => let xy := x.pow y; (dxy'*x.log*xy, dxy'*y/x*xy) by sorry,
  abbrev ℛ := let xy := x.pow y; (xy, λ dxy' => (dxy'*x.log*xy, dxy'*y/x*xy)) by sorry

-- These theorems have to be done by had as `function_property` can't handle dependant types
-- and `ite` has this `(c : Prop) [Decidable c]` which is currently not handled well

@[fun_trans]
theorem ite.arg_te.differential_simp' [UnsafeAD] 
  {X Y} [Vec X] [Vec Y] 
  (c : X → Prop) [∀ x, Decidable (c x)] 
  (t : X → Y) (e : X → Y) [IsSmooth t] [IsSmooth e]
  : ∂ (λ x => if c x then t x else e x)
    =
    λ x dx => if c x then ∂ t x dx else ∂ e x dx 
  := UnsafeAD.kaboom.elim

@[fun_trans]
theorem ite.arg_te.tangentMap_simp' [UnsafeAD] 
  {X Y} [Vec X] [Vec Y] 
  (c : X → Prop) [∀ x, Decidable (c x)] 
  (t : X → Y) (e : X → Y) [IsSmooth t] [IsSmooth e]
  : ∂ (λ x => if c x then t x else e x)
    =
    λ x dx => if c x then ∂ t x dx else ∂ e x dx 
  := UnsafeAD.kaboom.elim


-- What should we do about `c x` on rhs? Or adjoint just does not exist?
-- @[fun_trans]
-- theorem ite.arg_te.adjoint_simp' 
--   [inst : UnsafeAD] {X Y} [SemiHilbert X] [SemiHilbert Y] 
--   (c : X → Prop) [∀ x, Decidable (c x)] 
--   (t : X → Y) (e : X → Y) [HasAdjoint t] [HasAdjoint e]
--   : (λ x => if c x then t x else e x)†
--     =
--     λ x' => if c x then t† x' else e† x'
--   := inst.kaboom.elim


@[fun_trans]
theorem ite.arg_te.adjointDifferential_simp' [UnsafeAD] 
  {X Y} [SemiHilbert X] [SemiHilbert Y] 
  (c : X → Prop) [∀ x, Decidable (c x)] 
  (t : X → Y) (e : X → Y) [HasAdjDiff t] [HasAdjDiff e]
  : ∂† (λ x => if c x then t x else e x)
    =
    λ x dx' => if c x then ∂† t x dx' else ∂† e x dx'
  := UnsafeAD.kaboom.elim

@[fun_trans]
theorem ite.arg_te.reverseDifferential_simp' [UnsafeAD] 
  {X Y} [SemiHilbert X] [SemiHilbert Y] 
  (c : X → Prop) [∀ x, Decidable (c x)] 
  (t : X → Y) (e : X → Y) [HasAdjDiff t] [HasAdjDiff e]
  : ℛ (λ x => if c x then t x else e x)
    =
    λ x => if c x then ℛ t x else ℛ e x
  := UnsafeAD.kaboom.elim

#eval show Lean.CoreM Unit from do

  addFunctionProperty ``ite ``differential #[1,2,3,4].toArraySet none ``ite.arg_te.differential_simp' none
  addFunctionProperty ``ite ``tangentMap #[1,2,3,4].toArraySet none ``ite.arg_te.tangentMap_simp' none
  addFunctionProperty ``ite ``adjointDifferential #[1,2,3,4].toArraySet none ``ite.arg_te.adjointDifferential_simp' none
  addFunctionProperty ``ite ``reverseDifferential #[1,2,3,4].toArraySet none ``ite.arg_te.reverseDifferential_simp' none





