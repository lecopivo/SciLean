import SciLean.Tactic.CustomSimp.Main
import SciLean.Core

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta.Simp

namespace SciLean

def myPre (e : Expr) : SimpM Step := 
  dbg_trace s!"Running pre on {e}"
  pure (Step.visit (Result.mk e none))

theorem diffOfLet {X Y Z} [Vec X] [Vec Y] [Vec Z] (g : X → Y) (f : X → Y → Z) [IsSmooth g] [IsSmooth f] [∀ x, IsSmooth (f x)]
  : (∂ λ x => 
      let y := g x
      f x y)
    =
    λ x dx =>
      let y  := g x
      let dy := ∂ g x dx
      ∂ f x dx y + ∂ (f x) y dy
:= by simp done

theorem diffOfLetSimple {X Y α} [Vec X] [Vec Y] (a : α) (f : X → α → Y) [IsSmooth (λ x => f x a)]
  : (∂ λ x => 
      let y := a
      f x y)
    =
    let y := a
    λ x dx =>
      ∂ (λ x => f x y) x dx
:= by simp done

#check @Zero.zero

abbrev vecZero (X : Type) [Vec X] : X := 0

#check @Eq
#check @sorryAx
def sorryAx' (α : Sort _) : α := sorryAx α false
-- Differentiate expression w.r.t to give free variables `xs = [(x₀,dx₀), (x₁, dx₁), ...]`
-- This differentiates only through lambdas and lets
open Lean Meta in
partial def diffExpr (lctx : LocalContext) (e : Expr) (xs : Array (Expr × Expr)) : MetaM (Option Expr) := do
Meta.withLCtx lctx (← getLocalInstances) do 
  match e with
  | Expr.letE xname xtype xval body _ => 
    let dxname := xname.appendBefore "d"
    let dxval? ← diffExpr lctx (xval.lowerLooseBVars 1 1) xs
    match dxval? with
    | some dxval =>
      withLetDecl xname xtype xval λ x => do
      withLetDecl dxname xtype dxval λ dx => do
        let dbody? ← diffExpr (← getLCtx) ((body.instantiate1 x).lowerLooseBVars 1 1) (xs.push (x,dx))
        match dbody? with
          | some dbody => mkLetFVars #[x,dx] dbody
          | none => pure none
    | none => 
      withLetDecl xname xtype xval λ x => do
        let dbody? ← diffExpr (← getLCtx) ((body.instantiate1 x).lowerLooseBVars 1 1) xs
        match dbody? with
          | some dbody => mkLetFVars #[x] dbody
          | none => pure none
  | _ => 
    let mut dfs : Array Expr := #[]

    -- TODO: Add this check!!! but we might have to add zero if we differentiate zero
    -- if (e.containsFVar x.fvarId!) then  

    for i in [0:xs.size] do

      let x  := xs[i].1
      let dx := xs[i].2
      if (e.containsFVar x.fvarId!) then 
        let xname := ((← getLCtx).getFVar! x).userName
        let xtype ← inferType x
        let f  := mkLambda (xname.appendAfter "'") default xtype (e.abstract #[x])
        let df ← mkAppM `SciLean.differential #[f.eta, x, dx]
        dfs := dfs.push df
    match dfs.size with
    | 0 => pure none
    | 1 => pure dfs[0]
    | _ => do pure $ some (← (dfs[1:]).foldlM (λ dfi df => mkAppM `HAdd.hAdd #[dfi,df]) dfs[0])
  

open Lean Meta in
partial def diffOnLet (e : Expr) : SimpM Step := do
  match e with  
  | Expr.app (Expr.app (Expr.app (Expr.app (Expr.app (Expr.const `SciLean.differential _ _) _ _) _ _) _ _) _ _) e' _ => 
      dbg_trace s!"Applying differential!"             
      match e' with
      | Expr.lam .. => 
        lambdaTelescope e' λ xs lb => do

          let zero ← mkAppOptM `SciLean.vecZero #[← inferType lb, none]

          let x := xs[0]
          let xname := ((← getLCtx).getFVar! x).userName
          let xtype ← inferType x
          let dxname := xname.appendBefore "d"
          let df ← 
            withLocalDecl dxname default xtype λ dx => do
              let df ← diffExpr (← getLCtx) lb #[(x,dx)]
              let df := df.getD zero
              dbg_trace s!"labda body to differentiate:\n{← ppExpr lb}\n"
              dbg_trace s!"differentiated:\n{← ppExpr df}\n\n"
              mkLambdaFVars (#[x,dx].append xs[1:]) df

          dbg_trace s!"Final fun:\n{← ppExpr df}\n"
          let eq ← mkAppM `Eq #[e,df]
          dbg_trace s!"eq {← ppExpr eq}"
          let proof ← mkAppM `SciLean.sorryAx' #[eq]
          dbg_trace s!"proof {← ppExpr proof}"
          dbg_trace s!"proof Type {← ppExpr (← inferType proof)}"

          pure (Step.visit (Result.mk df proof))
      | _ => pure (Step.visit (Result.mk e none))
  | _ => pure (Step.visit (Result.mk e none))

open Lean.Parser.Tactic in
syntax (name := autodiff_core) "autodiff_core " (config)? (discharger)? (&"only ")? ("[" (simpStar <|> simpErase <|> simpLemma),* "]")? (location)? : tactic

open Lean.Elab.Tactic in
@[tactic autodiff_core] def evalMySimp : Tactic := fun stx => do
  let r ← withMainContext <| mkSimpContext stx (eraseLocal := false)
  dbg_trace "Running my autodiff core"
  r.dischargeWrapper.with fun discharge? =>
    SciLean.Tactic.CustomSimp.simpLocation r.ctx discharge? r.fvarIdToLemmaId (expandOptLocation stx[5]) #[diffOnLet] #[]

@[irreducible] def foo (a b : Nat) := a + b
@[simp] theorem foo_simp (a b : Nat) : foo a b = a + b := by unfold foo; rfl 

-- example {X Y} [Vec X] [Vec Y] (g : X → X) (f : X → X → Y) [IsSmooth g] [IsSmooth f] [∀ x, IsSmooth (f x)]
--   : (∂ λ x => 
--       let y := g x
--       f y y)
--     =
--     hold
--     λ x dx =>
--       let y  := g x
--       let dy := ∂ g x dx
--       ∂ f y dy y + ∂ (f y) y dy
-- := by
--   autodiff_core (config := {zeta := false})
--   simp[hold]
--   done

example {X Y Z W} [Vec X] [Vec Y] [Vec Z] [Vec W] (g : W → X) (h : W → Y) (f : W → X → Y → Z) [IsSmooth h] [IsSmooth g] [IsSmooth f] [∀ x, IsSmooth (f x)]  [∀ x y, IsSmooth (f x y)]
  : (λ n : Nat => 
    (∂ λ x w : W => 
      let y := g x
      let z := h x
      f x y z))
    =
    λ n : Nat => 
    hold
    λ x dx w =>
      let y  := g x
      let dy := ∂ g x dx
      let z  := h x
      let dz := ∂ h x dx
      ∂ f x dx y z + ∂ (f x) y dy z + ∂ (f x y) z dz
:= by
  autodiff_core (config := {zeta := false, singlePass := true})
  -- autodiff_core (config := {zeta := false, singlePass := true})
  -- autodiff_core (config := {zeta := false, singlePass := true})
  -- autodiff_core (config := {zeta := false, singlePass := true})
  simp[hold]
  done

@[simp]
theorem diff_at_zero {X Y} [Vec X] [Vec Y] (f : X → Y) [IsSmooth f] (x : X) : ∂ f x 0 = 0 := sorry

example {X Y} [Vec X] [Vec Y] (a : α) (g : α → X) (f : X → X → Y) [IsSmooth (λ x => f x (g a))]
  : (λ n : Nat => (∂ λ x => 
      let y := g a
      f x y))
    = 
    λ n : Nat =>
    hold
    λ x dx =>
      let y := g a
      ∂ (λ x => f x y) x dx
:= by
  autodiff_core (config := {zeta := false})
  simp[hold]
  done

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

