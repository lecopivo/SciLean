import SciLean.Tactic.CustomSimp.Main
import SciLean.Tactic.CustomSimp.AllPrePost
import SciLean.Tactic.CustomSimp.DebugSimp

import SciLean.Tactic.AutoDiff.LetDiff
import SciLean.Core

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta.Simp

namespace SciLean


open Lean.Parser.Tactic in
syntax (name := autodiff_core) "autodiff_core " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

open Lean.Elab.Tactic in
open SciLean.Tactic.CustomSimp in
@[tactic autodiff_core] def evalMySimp : Tactic := fun stx => do
  let r ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  r.dischargeWrapper.with fun discharge? =>
    SciLean.Tactic.CustomSimp.simpLocation r.ctx discharge? r.fvarIdToLemmaId (expandOptLocation stx[5]) #[/- letDiff,-/ DebugSimp.pre, preRewriteAll] #[]

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

