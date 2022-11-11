import SciLean.Tactic.CustomSimp.Main
import SciLean.Tactic.CustomSimp.AllPrePost
-- import SciLean.Tactic.CustomSimp.DebugSimp

import SciLean.Tactic.AutoDiff.LetDiff
import SciLean.Core
import SciLean.Functions

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta.Simp

namespace SciLean
open Tactic.CustomSimp

open Lean.Parser.Tactic in
syntax (name := autodiff_core) "autodiff_core " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

open Lean.Elab.Tactic in
@[tactic autodiff_core] def autoDiffCore : Tactic := fun stx => do
  let { ctx, dischargeWrapper } ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  let usedSimps ← dischargeWrapper.with fun discharge? =>
    SciLean.Meta.CustomSimp.simpLocation ctx discharge? (expandOptLocation stx[5]) #[letDiff] #[]
  if tactic.simp.trace.get (← getOptions) then
    dbg_trace "warning: Runnig custom simp with tracing, not sure if it is working properly!"
    traceSimpCall stx usedSimps


open Lean.Parser.Tactic in
/-- `simp [thm]` performs simplification using `thm` and marked `@[simp]` lemmas.
See the `simp` tactic for more information. -/
syntax (name := autodiff_core_conv) "autodiff_core" (config)? (discharger)? (&" only")? (" [" (simpStar <|> simpErase <|> simpLemma),* "]")? : conv

open Lean.Elab.Tactic Lean.Elab.Tactic.Conv in
@[tactic autodiff_core_conv] def autoDiffCoreConv : Tactic := fun stx => withMainContext do
  let { ctx, dischargeWrapper, .. } ← mkSimpContext stx (eraseLocal := false)
  let lhs ← getLhs
  let (result, _) ← dischargeWrapper.with fun d? => SciLean.Meta.CustomSimp.simp lhs ctx (discharge? := d?) #[letDiff, preRewriteAll] #[]
  applySimpResult result

set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.unify false in
#check (∂ λ (x : ℝ) => let y := x*x; let z := x + y*x*x; x + y + z) rewrite_by (
  autodiff_core (config := {singlePass := true,  zeta := false});
  simp (config := {zeta := false}) only [];
  trace_state;)


-- set_option trace.Meta.Tactic.simp true in
-- set_option trace.Meta.Tactic.simp.rewrite false in
-- set_option trace.Meta.Tactic.simp.unify false in
-- #check (∂ λ (x : ℝ) => let y := x; let z := x + y; y + z) rewrite_by (
--   autodiff_core (config := {singlePass := true, zeta := false}); trace_state;)


-- This fails to apply `SciLean.diff_of_comp` because it `foo` can't be proven to be smooth
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.discharge true in
#check (∂ λ (x : ℝ) => let z := x^2; let foo := λ y => Math.sin (Math.exp y); foo (Math.cos z)) rewrite_by (autodiff_core (config := {singlePass := true, zeta := false}); simp (config := { zeta := false}) only []; trace_state;)



-- @[irreducible] def foo (a b : Nat) := a + b
-- @[simp] theorem foo_simp (a b : Nat) : foo a b = a + b := by unfold foo; rfl 

-- example {X Y Z W} [Vec X] [Vec Y] [Vec Z] [Vec W] (g : W → X) (h : W → Y) (f : W → X → Y → Z) [IsSmooth h] [IsSmooth g] [IsSmooth f] [∀ x, IsSmooth (f x)]  [∀ x y, IsSmooth (f x y)]
--   : (λ n : Nat => 
--     (∂ λ x w : W => 
--       let y := g x
--       let z := h x
--       f x y z))
--     =
--     λ n : Nat => 
--     hold
--     λ x dx w =>
--       let y  := g x
--       let dy := ∂ g x dx
--       let z  := h x
--       let dz := ∂ h x dx
--       ∂ f x dx y z + ∂ (f x) y dy z + ∂ (f x y) z dz
-- := by
--   autodiff_core (config := {zeta := false, singlePass := true})

--   -- autodiff_core (config := {zeta := false, singlePass := true})
--   -- autodiff_core (config := {zeta := false, singlePass := true})
--   -- autodiff_core (config := {zeta := false, singlePass := true})
--   simp[hold]
--   admit

-- @[simp]
-- theorem diff_at_zero {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x : X) : ∂ f x 0 = 0 := sorry

-- example {X Y} [Vec X] [Vec Y] (a : α) (g : α → X) (f : X → X → Y) [IsSmooth (λ x => f x (g a))]
--   : (λ n : Nat => (∂ λ x => 
--       let y := g a
--       f x y))
--     = 
--     λ n : Nat =>
--     hold
--     λ x dx =>
--       let y := g a
--       ∂ (λ x => f x y) x dx
-- := by
--   autodiff_core (config := {zeta := false})
--   simp[hold]
--   done

-- example {X Y} [Vec X] [Vec Y] (a : α) (g : α → X) (f : X → X → Y) [IsSmooth (f (g a))]
--   : (∂ λ x => 
--       let y := g a
--       f y x)
--     =
--     hold
--     λ x dx =>
--       let y  := g a
--       ∂ (f y) x dx
-- := by
--   autodiff_core (config := {zeta := false})
--   simp[hold]
--   done

