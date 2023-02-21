import Mathlib.Lean.Expr
import SciLean.Tactic.CustomSimp.Main
-- import SciLean.Core.Differential

import Lean.Meta
import Lean.Parser
import Lean.Elab

-- namespace Lean.Elab.Tactic
open Lean Meta.Simp

namespace SciLean

-- def myPre (e : Expr) : SimpM Step := 
--   dbg_trace s!"Running pre on {e}"
--   pure (Step.visit (Result.mk e none))

-- theorem diffOfLet {X Y Z} [Vec X] [Vec Y] [Vec Z] (g : X → Y) (f : X → Y → Z) [IsSmoothT g] [IsSmoothNT 2 f]
--   : (∂ λ x => 
--       let y := g x
--       f x y)
--     =
--     λ x dx =>
--       let y  := g x
--       let dy := ∂ g x dx
--       ∂ f x dx y + ∂ (f x) y dy
-- := by simp[tangentMap]; done

-- theorem diffOfLetSimple {X Y α} [Vec X] [Vec Y] (a : α) (f : X → α → Y) [IsSmooth (λ x => f x a)]
--   : (∂ λ x => 
--       let y := a
--       f x y)
--     =
--     let y := a
--     λ x dx =>
--       ∂ (λ x => f x y) x dx
-- := by simp; done

-- abbrev vecZero (X : Type) [Vec X] : X := 0

-- -- Differentiate expression w.r.t to give free variables `xs = [(x₀,dx₀), (x₁, dx₁), ...]`
-- -- This differentiates only through lambdas and lets
-- #check @differential

def sorryAx' (α : Sort _) : α := sorryAx α false

open Lean Meta in
def diffLet (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e.app4? `SciLean.differential with
  | none => pure none
  | some (_,_,_,e') =>
    dbg_trace s!"Differential application {← Lean.Meta.ppExpr e}"
    match e' with
    | Expr.lam .. => lambdaLetTelescope e' λ xs b => do
      let x := xs[0]!
      let xDecl ← getFVarLocalDecl x
      -- find first let that depends on `x`
      let yIdx? ← xs.findIdxM? 
        (λ xi => do 
          let xiDecl ← getFVarLocalDecl xi
          pure <| xiDecl.isLet ∧ xiDecl.value.containsFVar xDecl.fvarId)
      match yIdx? with
      | none => pure none
      | some yIdx => 
        let y := xs[yIdx]!
        let yDecl ← getFVarLocalDecl y
        let yFun  ← mkLambdaFVars #[x] yDecl.value

        -- withLocalDecl (xDecl.userName.appendAfter "'") xDecl.binderInfo xDecl.type λ x' =>
        withLocalDecl (xDecl.userName |>.appendBefore "d") xDecl.binderInfo xDecl.type λ dx => do

        -- replace `x` with `x'` in the type of `y`
        -- This should not really happen as differentiating dependently typed functions is currently not possible
        -- let yType ← mkAppM' (← mkLambdaFVars #[x] yDecl.type) #[x']

        -- withLetDecl (yDecl.userName.appendAfter "'") yType (← mkAppM' yFun #[x']) λ y' => do
        -- let b := b.replaceFVar y y'
        -- let xs := xs.map λ xi => xi.replaceFVar y y'
        dbg_trace "hihi {← ppExpr yFun}"
        let dyVal ← mkAppM' (← mkAppM `SciLean.differential #[yFun]) #[x, dx]
        dbg_trace "hoho {← ppExpr dyVal}"
        withLetDecl (yDecl.userName |>.appendAfter "'" |>.appendBefore "d") yDecl.type dyVal λ dy => do


        let bXFun ← mkLambdaFVars (#[x].append xs[yIdx+1:]) b
        let bYFun := Expr.lam yDecl.userName (← inferType y) (b.abstract #[y]) default

        dbg_trace "hehe {← ppExpr bXFun}"
        dbg_trace "huhu {← ppExpr bYFun}"
        let fdx ← mkAppM' (← mkAppM `SciLean.differential #[bXFun]) #[x, dx]
        let fdy ← mkAppM' (← mkAppM `SciLean.differential #[bYFun]) #[y, dy]

        dbg_trace "bla {← ppExpr fdx}"
        dbg_trace "blo {← ppExpr fdy}"


        let vars := #[x,dx] 
          |>.append xs[1:yIdx]
          |>.append #[y, dy]
          |>.append xs[yIdx+1:]

        dbg_trace "vars: {vars}"
        dbg_trace "vars: {← vars.mapM λ v => ppExpr v}"

        let b' ← mkAppM ``HAdd.hAdd #[fdx, fdy]

        dbg_trace "b': {b'}"
        dbg_trace "b': {← ppExpr b'}"

        let e'' ← mkLambdaFVars vars b'

        dbg_trace "e'': {e''}"
        dbg_trace "e'': {← ppExpr e''}"

        
        let eqType ← mkAppM ``Eq #[e, e'']
        -- TODO: Currently we sorry equality proof
        let eqProof ← mkAppM ``sorryAx' #[eqType]

        pure <| some (e'', eqProof)
    | _ => pure none


open Lean Meta in
/-- Differentiate `e` with respect to free variables `dvars = [(x₁, dx₁), ..., (xₙ, dxₙ)]` 

Returns `none` if `e` does not depend on any of the `x₁, ..., xₙ`. -/
def diffFVars (dvars : Array (Expr × Expr)) (e : Expr) : MetaM (Option Expr) := do 

  let fstIdx? := dvars.findIdx? (λ (xi, _) => e.containsFVar xi.fvarId!)

  match fstIdx? with
  | none => pure none
  | some fstIdx => do
    let D := λ (e' : Expr) ((x, dx) : Expr × Expr) => do
      let xDecl ← getFVarLocalDecl x
      let f := Expr.lam xDecl.userName xDecl.type (e'.abstract #[x]) default
      mkAppM' (← mkAppM `SciLean.differential #[f]) #[x, dx]
    let e' ← dvars[fstIdx+1:].foldlM (init := ← D e dvars[fstIdx]!) 
      λ e' (xi, dxi) => do
        mkAppM ``HAdd.hAdd #[e', ← D e (xi, dxi)]

    pure (some e')



open Lean Meta in
def diffLet' (e : Expr) : MetaM (Option (Expr × Expr)) := do

  if ¬(e.isAppOf `SciLean.differential) then
    return none
  else
    match e.getArg? 5 with
    | none => return none
    | some e' => do
    match e' with
    | Expr.lam .. => lambdaLetTelescope e' λ xs b => do
      let x := xs[0]!
      let xDecl ← getFVarLocalDecl x

      if xDecl.isLet then 
        return none

      withLocalDecl (xDecl.userName |>.appendBefore "d") xDecl.binderInfo xDecl.type λ dx => do

      -- Comput differentials of all let bindings
      let (lctx, vars, dvars) ← xs[1:].foldlM (init := (← getLCtx, #[x,dx], #[(x,dx)])) 
        (λ (lctx, vars, dvars) xi => do
          withLCtx lctx (← getLocalInstances) do 
            let xiDecl ← getFVarLocalDecl xi
            if ¬xiDecl.isLet then
              pure (lctx, vars.push xi, dvars)
            else
              match ← diffFVars dvars xiDecl.value with
              | none => pure (lctx, vars.push xi, dvars)
              | some dxiVal => do
                withLetDecl (xiDecl.userName |>.appendBefore "d") xiDecl.type dxiVal λ dxi => do
                  pure (← getLCtx, vars.append #[xi, dxi], dvars.push (xi, dxi))) 
      
      -- no let binding worth differentiating through found
      if dvars.size = 1 then
        return none

      withLCtx lctx (← getLocalInstances) do
        match ← diffFVars dvars b with
        | none => pure none
        | some db => do
          let e'' ← mkLambdaFVars vars db

          let eqType ← mkAppM ``Eq #[e, e'']
          -- TODO: Currently we sorry equality proof
          let eqProof ← mkAppM ``sorryAx' #[eqType]

          pure <| some (e'', eqProof)
    | _ => pure none



open Lean Meta in
partial def letDiff (e : Expr) : SimpM Step := do
  match ← diffLet' e with
  | some (e', proof) => pure (Step.visit (Result.mk e' proof 0))
  | none => pure (Step.visit { expr := e })
