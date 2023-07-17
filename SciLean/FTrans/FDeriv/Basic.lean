import SciLean.Tactic.FTrans.Basic

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear


import SciLean.Tactic.LSimp.Elab
import SciLean.FunctionSpaces.ContinuousLinearMap.Basic
import SciLean.FunctionSpaces.Differentiable.Basic

namespace SciLean

set_option linter.unusedVariables false

variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

theorem fderiv.id_rule 
  : (fderiv K fun x : X => x) = fun _ => fun dx =>L[K] dx
  := by ext x dx; simp


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
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz := 
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
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz := 
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


def fderiv.discharger : Expr → SimpM (Option Expr) :=
  FTrans.tacticToDischarge (Syntax.mkLit ``tacticDifferentiable "differentiable")

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

  identityTheorem := ``fderiv.id_rule 
  constantTheorem := ``fderiv.const_rule

  replaceFTransFun e f := 
    if e.isAppOf ``fderiv then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  applyLambdaLetRule e := do
    match e.getArg? 8 with
    | .some (.lam xName xType 
              (.letE yName yType yVal body _) bi) => do

      let ruleName := ``fderiv.let_rule

      let thm : SimpTheorem := {
        proof := mkConst ruleName
        origin := .decl ruleName
        rfl := false
      }

      if let some result ← Meta.Simp.tryTheorem? e thm fderiv.discharger then
        return Simp.Step.visit result

      return none
    | _ => return none

  applyLambdaLambdaRule e := do
    match e.getArg? 8 with
    | .some (.lam xName xType 
              (.lam yName yType body _) _) => do

      let ruleName := ``fderiv.pi_rule

      let thm : SimpTheorem := {
        proof := mkConst ruleName
        origin := .decl ruleName
        rfl := false
      }

      if let some result ← Meta.Simp.tryTheorem? e thm fderiv.discharger then
        return Simp.Step.visit result

      return none
    | _ => return none


  discharger := fderiv.discharger

#eval show Lean.CoreM Unit from do
  FTrans.FTransExt.insert ``fderiv fderiv.ftransInfo



--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------


-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem _root_.Prod.mk.arg_fstsnd.fderiv_at_comp
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (g x, f x)) x
    =
    fun dx =>L[K]
      (fderiv K g x dx, fderiv K f x dx) := 
by 
  sorry


@[ftrans_rule]
theorem _root_.Prod.mk.arg_fstsnd.fderiv_comp
  (x : X)
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Z) (hf : Differentiable K f)
  : fderiv K (fun x => (g x, f x)) x
    =
    fun dx =>L[K]
      (fderiv K g x dx, fderiv K f x dx) := 
by 
  sorry

 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem _root_.Prod.fst.arg_self.fderiv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (f x).1) x
    =
    fun dx =>L[K] (fderiv K f x dx).1
:= sorry


@[ftrans_rule]
theorem _root_.Prod.fst.arg_self.fderiv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv K (fun x => (f x).1)
    =
    fun x => fun dx =>L[K] (fderiv K f x dx).1
:= sorry


@[ftrans_rule]
theorem _root_.Prod.fst.arg_self.fderiv
  : fderiv K (fun xy : X×Y => xy.1)
    =  
    fun _ => fun dxy =>L[K] dxy.1
:= by ftrans; sorry



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem _root_.Prod.snd.arg_self.fderiv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (f x).2) x
    =
    fun dx =>L[K] (fderiv K f x dx).2
:= sorry


@[ftrans_rule]
theorem _root_.Prod.snd.arg_self.fderiv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv K (fun x => (f x).2)
    =
    fun x => fun dx =>L[K] (fderiv K f x dx).2
:= sorry

@[ftrans_rule]
theorem _root_.Prod.snd.arg_self.fderiv
  : fderiv K (fun xy : X×Y => xy.2)
    =  
    fun _ => fun dxy =>L[K] dxy.2
:= by ftrans; sorry



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem _root_.HAdd.hAdd.arg_a4a5.fderiv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv K fun x => f x + g x) x
    =
    fun dx =>L[K]
      fderiv K f x dx + fderiv K g x dx
  := sorry


@[ftrans_rule]
theorem _root_.HAdd.hAdd.arg_a4a5.fderiv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x + g x)
    =
    fun x => fun dx =>L[K]
      fderiv K f x dx + fderiv K g x dx
  := sorry
