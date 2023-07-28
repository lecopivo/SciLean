
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv 


import SciLean.FunctionSpaces.ContinuousLinearMap.Notation
import SciLean.FunctionSpaces.Differentiable.Basic
import SciLean.Tactic.FTrans.Basic


namespace SciLean

set_option linter.unusedVariables false

variable 
  {K : Type _} [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

noncomputable
def cderiv (K : Type _) [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  (f : X → Y) (x dx : X) : Y := fderiv K f x dx

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

theorem cderiv.id_rule 
  : (cderiv K fun x : X => x) = fun _ => fun dx => dx
  := by unfold cderiv; ext x dx; simp

theorem cderiv.const_rule (x : X)
  : (cderiv K fun _ : Y => x) = fun _ => fun dx => 0
  := by unfold cderiv; ext x dx; simp

theorem cderiv.comp_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : Y → Z) (hf : DifferentiableAt K f (g x))
  : (cderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>
      let dy := cderiv K g x dx
      let dz := cderiv K f y dy
      dz :=
by 
  unfold cderiv; 
  rw[show (fun x => f (g x)) = f ∘ g by rfl]
  rw[fderiv.comp x hf hg]
  ext dx; simp

theorem cderiv.comp_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : Y → Z) (hf : Differentiable K f)
  : (cderiv K fun x : X => f (g x))
    =
    fun x => 
      let y := g x
      fun dx =>
        let dy := cderiv K g x dx
        let dz := cderiv K f y dy
        dz :=
by 
  unfold cderiv
  funext x;
  rw[show (fun x => f (g x)) = f ∘ g by rfl]
  rw[fderiv.comp x (hf (g x)) (hg x)]
  ext dx; simp


theorem cderiv.let_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Y → Z) (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x))
  : (cderiv K
      fun x : X =>
        let y := g x
        f x y) x
    =
    let y  := g x
    fun dx =>
      let dy := cderiv K g x dx
      let dz := cderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by
  unfold cderiv
  have h : (fun x => f x (g x)) = (fun xy : X×Y => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  conv => 
    lhs
    rw[h]
    rw[fderiv.comp x hf (DifferentiableAt.prod (by simp) hg)]
    rw[DifferentiableAt.fderiv_prod (by simp) hg]
  ext dx; simp[ContinuousLinearMap.comp]
  rfl


theorem cderiv.let_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Y → Z) (hf : Differentiable K fun xy : X×Y => f xy.1 xy.2)
  : (cderiv K fun x : X =>
       let y := g x
       f x y)
    =
    fun x => 
      let y  := g x
      fun dx =>
        let dy := cderiv K g x dx
        let dz := cderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
        dz := 
by
  funext x
  apply cderiv.let_rule_at x _ (hg x) _ (hf (x,g x))


theorem cderiv.pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (cderiv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx => fun i =>
      cderiv K (f i) x dx := 
by
  unfold cderiv
  rw[fderiv_pi hf]
  simp


theorem cderiv.pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (cderiv K fun (x : X) (i : ι) => f i x)
    = 
    fun x => fun dx => fun i =>
      cderiv K (f i) x dx
  := by unfold cderiv; funext x; rw[fderiv_pi (fun i => hf i x)]; simp



-- Register `cderiv` as function transformation --------------------------------
--------------------------------------------------------------------------------
#exit
open Lean Meta Qq

def cderiv.discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `cderiv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  return proof?

open Lean Elab Term FTrans
def cderiv.ftransExt : FTransExt where
  ftransName := ``cderiv

  getFTransFun? e := 
    if e.isAppOf ``cderiv then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``cderiv then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  identityRule     := .some <| .thm ``cderiv.id_rule
  constantRule     := .some <| .thm ``cderiv.const_rule
  compRule         := .some <| .thm ``cderiv.comp_rule
  lambdaLetRule    := .some <| .thm ``cderiv.let_rule
  lambdaLambdaRule := .some <| .thm ``cderiv.pi_rule

  discharger := cderiv.discharger


-- register cderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``cderiv, cderiv.ftransExt))


end SciLean

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

variable 
  {K : Type _} [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

open SciLean

-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.cderiv_at_comp
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Z) (hf : DifferentiableAt K f x)
  : cderiv K (fun x => (g x, f x)) x
    =
    fun dx =>
      (cderiv K g x dx, cderiv K f x dx) := 
by 
  unfold SciLean.cderiv
  rw[DifferentiableAt.fderiv_prod hg hf]
  simp


@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.cderiv_comp
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Z) (hf : Differentiable K f)
  : cderiv K (fun x => (g x, f x))
    =    
    fun x => fun dx =>
      (cderiv K g x dx, cderiv K f x dx) := 
by 
  unfold cderiv; funext x; rw[DifferentiableAt.fderiv_prod (hg x) (hf x)]; simp

 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Prod.fst.arg_self.cderiv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : cderiv K (fun x => (f x).1) x
    =
    fun dx => (cderiv K f x dx).1 := 
by
  unfold cderiv
  rw[fderiv.fst hf]
  simp


@[ftrans_rule]
theorem Prod.fst.arg_self.cderiv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : cderiv K (fun x => (f x).1)
    =
    fun x => fun dx => (cderiv K f x dx).1 := 
by
  unfold cderiv
  funext x; rw[fderiv.fst (hf x)]; simp


@[ftrans_rule]
theorem Prod.fst.arg_self.cderiv
  : cderiv K (fun xy : X×Y => xy.1)
    =  
    fun _ => fun dxy => dxy.1
:= by unfold cderiv; funext xy; rw[fderiv_fst]; simp


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Prod.snd.arg_self.cderiv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : cderiv K (fun x => (f x).2) x
    =
    fun dx => (cderiv K f x dx).2 := 
by
  unfold cderiv
  rw[fderiv.snd hf]
  simp


@[ftrans_rule]
theorem Prod.snd.arg_self.cderiv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : cderiv K (fun x => (f x).2)
    =
    fun x => fun dx => (cderiv K f x dx).2 :=
by
  unfold cderiv
  funext x; rw[fderiv.snd (hf x)]
  simp

@[ftrans_rule]
theorem Prod.snd.arg_self.cderiv
  : cderiv K (fun xy : X×Y => xy.2)
    =  
    fun _ => fun dxy => dxy.2
:= by unfold cderiv; funext xy; rw[fderiv_snd]; simp



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.cderiv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (cderiv K fun x => f x + g x) x
    =
    fun dx =>
      cderiv K f x dx + cderiv K g x dx
  := by unfold cderiv; rw[fderiv_add hf hg]; simp


@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.cderiv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (cderiv K fun x => f x + g x)
    =
    fun x => fun dx =>
      cderiv K f x dx + cderiv K g x dx
  := by unfold cderiv; funext x; rw[fderiv_add (hf x) (hg x)]; simp


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HSub.hSub.arg_a4a5.cderiv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (cderiv K fun x => f x - g x) x
    =
    fun dx =>
      cderiv K f x dx - cderiv K g x dx
  := by unfold cderiv; rw[fderiv_sub hf hg]; simp


@[ftrans_rule]
theorem HSub.hSub.arg_a4a5.cderiv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (cderiv K fun x => f x - g x)
    =
    fun x => fun dx =>
      cderiv K f x dx - cderiv K g x dx
  := by unfold cderiv; funext x; rw[fderiv_sub (hf x) (hg x)]; simp



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Neg.neg.arg_a2.cderiv_at_comp
  (x : X) (f : X → Y)
  : (cderiv K fun x => - f x) x
    =
    fun dx =>
      - cderiv K f x dx
  := by unfold cderiv; rw[fderiv_neg]; simp


@[ftrans_rule]
theorem Neg.neg.arg_a2.cderiv_comp
  (f : X → Y)
  : (cderiv K fun x => - f x)
    =
    fun x => fun dx =>
      - cderiv K f x dx
  := by unfold cderiv; funext x; rw[fderiv_neg]; simp


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HMul.hMul.arg_a4a5.cderiv_at_comp
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (x : X) (f g : X → Y)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (cderiv K fun x => f x * g x) x
    =
    let fx := f x
    let gx := g x
    fun dx =>
      (cderiv K g x dx) * fx + (cderiv K f x dx) * gx := 
by
  unfold cderiv
  ext dx
  simp[fderiv_mul hf hg, mul_comm]; rfl


@[ftrans_rule]
theorem HMul.hMul.arg_a4a5.cderiv_comp
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (f g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (cderiv K fun x => f x * g x)
    =
    fun x => 
      let fx := f x
      let gx := g x
      fun dx =>
        (cderiv K g x dx) * fx + (cderiv K f x dx) * gx := 
by 
  unfold cderiv
  funext x; ext dx;
  simp[fderiv_mul (hf x) (hg x), mul_comm]
  rfl


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem SMul.smul.arg_a3a4.cderiv_at_comp
  (x : X) (f : X → K) (g : X → Y) 
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (cderiv K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>
      k • (cderiv K g x dx) + (cderiv K f x dx) • y := 
by
  unfold cderiv
  rw[fderiv_smul hf hg]
  rfl


@[ftrans_rule]
theorem SMul.smul.arg_a3a4.cderiv_comp
  (f : X → K) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (cderiv K fun x => f x • g x)
    =
    fun x => 
      let k := f x
      let y := g x
      fun dx =>
        k • (cderiv K g x dx) + (cderiv K f x dx) • y := 
by 
  unfold cderiv;
  funext x; rw[fderiv_smul (hf x) (hg x)]
  rfl


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HDiv.hDiv.arg_a4a5.cderiv_at_comp
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K)
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : (cderiv R fun x => f x / g x) x
    =
    let k := f x
    let k' := g x
    fun dx =>
      ((cderiv R f x dx) * k' - k * (cderiv R g x dx)) / k'^2 := 
by
  unfold cderiv
  have h : ∀ (f : R → K) x dx, fderiv R f x dx = dx • deriv f x := by simp[deriv]; sorry
  ext dx; simp[h]; rw[deriv_div hf hg hx]; sorry -- rw[smul_div' dx (deriv f x * g x - f x * deriv g x) (g x ^ 2)]; simp[smul_div',smul_sub]


@[ftrans_rule]
theorem HDiv.hDiv.arg_a4a5.cderiv_comp
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (f : R → K) (g : R → K) 
  (hf : Differentiable R f) (hg : Differentiable R g) (hx : ∀ x, g x ≠ 0)
  : (cderiv R fun x => f x / g x)
    =
    fun x => 
      let k := f x
      let k' := g x
      fun dx =>
        ((cderiv R f x dx) * k' - k * (cderiv R g x dx)) / k'^2 := 
by
  funext x
  apply HDiv.hDiv.arg_a4a5.cderiv_at_comp x f g (hf x) (hg x) (hx x)
