import SciLean.Tactic.FTrans.Basic

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear


import SciLean.Tactic.LSimp.Elab
import SciLean.FunctionSpaces.ContinuousLinearMap.Basic
import SciLean.FunctionSpaces.Differentiable.Basic

import SciLean.Profile

namespace SciLean

-- open Filter Asymptotics ContinuousLinearMap Set Metric

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false

variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]


@[ftrans]
theorem fderiv.id_rule 
  : (fderiv K fun x : X => x) = fun _ => fun dx =>L[K] dx
  := by ext x dx; simp


@[ftrans]
theorem fderiv.const_rule (x : X)
  : (fderiv K fun _ : Y => x) = fun _ => fun dx =>L[K] 0
  := by ext x dx; simp


theorem fderiv.let_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Y → Z) (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x))
  : (fderiv K 
      fun x : X => 
        let y := g x 
        f x y) x
    =
    fun dx =>L[K] 
      let y  := g x
      let dg := fderiv K g x
      let df := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y)
      df (dx, (dg dx)) := 
by 
  have h : (fun x => f x (g x)) = (fun xy : X×Y => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  rw[h]
  rw[fderiv.comp x hf (DifferentiableAt.prod (by simp) hg)]
  rw[DifferentiableAt.fderiv_prod (by simp) hg]
  ext dx; simp[ContinuousLinearMap.comp]
  rfl


theorem fderiv.let_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Y → Z) (hf : Differentiable K fun xy : X×Y => f xy.1 xy.2)
  : (fderiv K fun x : X =>
       let y := g x
       f x y)
    =
    fun x => fun dx =>L[K]
      let y  := g x
      let dg := fderiv K g x
      let df := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y)
      df (dx, (dg dx)) := 
by
  funext x
  apply fderiv.let_rule_at x _ (hg x) _ (hf (x,g x))


theorem fderiv.pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (fderiv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := fderiv_pi hf


theorem fderiv.pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (fderiv K fun (x : X) (i : ι) => f i x)
    = 
    fun x => fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := by funext x; apply fderiv_pi (fun i => hf i x)


-- Register `fderiv` as function transformation --------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

open Lean Elab Term
def fderiv.ftransInfo : FTrans.Info where
  getFTransFun? e := 
    if e.isAppOf ``fderiv then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fderiv then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  applyLambdaLetRule e :=
    match e.getArg? 8 with
    | .some (.lam xName xType 
              (.letE yName yType yVal body _) bi) => do

      let g := Expr.lam xName xType yVal bi  
      let f := Expr.lam xName xType (Expr.lam yName yType body default) bi  

      let K := e.getArg! 0

      let hgType ← mkAppM ``Differentiable #[K,g]
      let hfType ← mkAppM ``Differentiable #[K, ← mkUncurryFun 2 f]
      let hg ← mkSorry hgType false -- mkFreshExprMVar hgType
      -- let hg ← mkFreshExprMVar hgType
      -- let _ ← Elab.runTactic hg.mvarId! (← `(tactic| aesop))
      let hf ← mkSorry hfType false
      
      
      let proof ← mkAppM ``fderiv.let_rule #[g,hg,f,hf]
      let rhs := (← inferType proof).getArg! 2

      -- let goal : MVarId := sorry


      dbg_trace "g = {← ppExpr g}"
      dbg_trace "f = {← ppExpr f}"
      dbg_trace "rhs = {← ppExpr rhs}"
       return .some (.visit (.mk rhs proof 0))
    | _ => return none

  applyLambdaLambdaRule e := return none

  discharger := FTrans.tacticToDischarge (Syntax.mkLit ``tacticDifferentiable "differentiable")

#eval show Lean.CoreM Unit from do
  FTrans.FTransExt.insert ``fderiv fderiv.ftransInfo


--------------------------------------------------------------------------------


@[ftrans, ftrans_rule]
theorem _root_.HAdd.hAdd.arg_a4a5.fderiv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x + g x)
    =
    fderiv K f + fderiv K g
  := sorry

set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
example
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x + g x)
    =
    fderiv K f + fderiv K g
  := by
  ftrans only


set_option trace.Meta.Tactic.simp.unify true in
@[ftrans]
theorem _root_.HAdd.hAdd.arg_a5.fderiv'
  (y : Y) 
  : (fderiv K (fun y' => HAdd.hAdd y y'))
    =
    fun y => fun dy =>L[K] dy
  := by 
  ftrans only
  ftrans only

@[ftrans]
theorem _root_.HAdd.hAdd.arg_a5.fderiv''
  (y : Y) 
  : (fderiv K (fun y' => y + y'))
    =
    fun y => fun dy =>L[K] dy
  := by ftrans only 

set_option trace.Meta.Tactic.simp.unify true in
@[ftrans]
theorem _root_.HAdd.hAdd.arg_a4.fderiv
  (y : Y) 
  : (fderiv K (fun y' => y' + y))
    =
    fun y => fun dy =>L[K] dy
  := by ftrans only  


#eval show CoreM Unit from do
  IO.println "hihi"
  let s := FTrans.FTransRulesExt.getState (← getEnv)
  IO.println s.toList


set_option trace.Meta.Tactic.ftrans.step true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
@[ftrans]
theorem _root_.HAdd.hAdd.arg_a5.fderiv
  (y : Y) 
  : (fderiv K fun y' => y + y')
    =
    fun y => fun dy =>L[K] dy := 
by 
  -- rw[HAdd.hAdd.arg_a4a5.fderiv_comp]
  -- rw[HAdd.hAdd.arg_a4a5.fderiv_comp _ _ (by differentiable) (by differentiable)]
  ftrans only
  ext; simp

#exit
-- @[ftrans]
-- theorem _root_.HAdd.hAdd.arg_a5.fderiv_comp
--   (x : X) (f : X → Y) (hf : Differentiable K f)
--   : (fderiv K (HAdd.hAdd)
--     =
--     fderiv K f + fderiv K g 
--   := sorry


@[differentiable]
theorem _root_.HAdd.hAdd.arg_a4a5.Differentiable
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : Differentiable K fun x => f x + g x
  := sorry


-- Prod.fst

@[ftrans]
theorem _root_.Prod.fst.arg_self.fderiv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (f x).1) x
    =
    fun dx =>L[K] (fderiv K f x dx).1
:= sorry

@[ftrans]
theorem _root_.Prod.fst.arg_self.fderiv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv K (fun x => (f x).1)
    =
    fun x => fun dx =>L[K] (fderiv K f x dx).1
:= sorry

@[ftrans_simp ↓ high]
theorem _root_.Prod.fst.arg_self.fderiv
  : fderiv K (fun xy : X×Y => xy.1)
    =
    fun _ => fun dxy =>L[K] dxy.1
:= sorry


-- Prod.snd

@[ftrans]
theorem _root_.Prod.snd.arg_self.fderiv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (f x).2) x
    =
    fun dx =>L[K] (fderiv K f x dx).2
:= sorry

@[ftrans]
theorem _root_.Prod.snd.arg_self.fderiv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv K (fun x => (f x).2)
    =
    fun x => fun dx =>L[K] (fderiv K f x dx).2
:= sorry

@[ftrans_simp ↓ high]
theorem _root_.Prod.snd.arg_self.fderiv
  : fderiv K (fun xy : X×Y => xy.2)
    =
    fun _ => fun dxy =>L[K] dxy.2
:= sorry




-- do
--     let goal ← mkFreshExprMVar e
--     try 
      
--       let (_, _) ← Elab.runTactic goal.mvarId! (← `(tactic| aesop))
--       let result ← instantiateMVars goal
--       if result.hasExprMVar then
--         return none
--       else
--         return none
--     catch _ => 
--       return none
    -- match e.getArg? 8 with
    -- | .some (.lam xName xType 
    --           (.lam yName yType yVal body _) bi) => do

    -- | _ => return none



set_option trace.Meta.Tactic.simp true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.ftrans.step true in
-- @[ftrans]
theorem _root_.HAdd.hAdd.arg_a4.fderiv_comp
  (y : Y) (f : X → Y) (hf : Differentiable K f)
  : (fderiv K fun x => f x + y)
    =
    fderiv K f
  := by ftrans only; simp; rfl

#exit


example :
  (fderiv K λ x : X => x)
  =
  fun _ => fun dx =>L[K] dx
:= 
  by ftrans only

example (x : X) :
  (fderiv K λ _ : Y => x)
  =
  fun _ => fun dx =>L[K] 0
:= 
  by ftrans only

theorem hoho (f : X → X) (hf : Differentiable K f) :
  (fderiv K λ x : X => (x + f (f (f x))) + (x + x))
  =
  fun _ => 0
  := by
  ftrans only
  ext x dx; simp
  sorry

example (x' : X) :
  (fderiv K (HAdd.hAdd x'))
  =
  fun _ => 0
  := by
  ftrans only
  ftrans only
  rw [HAdd.hAdd.arg_a4a5.fderiv_comp _ _  (by simp) (by simp)]
  sorry


set_option trace.Meta.Tactic.simp.rewrite true in
example :
  (fderiv K λ x : X×X => x.1)
  =
  fun x => fun dx =>L[K] dx.1
  := by ftrans only

#exit

example (x' : X) :
  (fderiv K λ x : X => x + x')
  =
  fun _ => fun dx =>L[K] dx
  := by
 ftrans only; simp
 ext x dx; simp


-- set_option pp.all true 
example :
  (fderiv K λ x : X => 
    let y := x + x
    x + y)
  =
  fun _ => 0
:= by
   ftrans only
   ftrans only
   sorry

-- example : Differentiable K fun x : (X×X) => x.1 + x.2 := by continuity



example : (Differentiable K fun x : X => x) = True := by simp
theorem hoho : (Differentiable K fun x : X => 
        let y := x + x
        y) = True := by aesop

-- example : Continuous fun x : (X×X) => x.1 + x.2 := by continuity
