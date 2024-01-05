
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv 

import SciLean.Tactic.FTrans.Basic

import SciLean.Core.FunctionPropositions.IsContinuousLinearMap
import SciLean.Core.FunctionPropositions.DifferentiableAt
import SciLean.Core.FunctionPropositions.Differentiable

namespace SciLean

variable 
  {K : Type _} [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------
variable (K)
variable (X)
theorem fderiv.id_rule 
  : (fderiv K fun x : X => x) = fun _ => fun dx =>L[K] dx
  := by ext x dx; simp
variable {X}

variable (Y)
theorem fderiv.const_rule (x : X)
  : (fderiv K fun _ : Y => x) = fun _ => fun dx =>L[K] 0
  := by ext x dx; simp
variable {Y}

variable (E)
theorem fderiv.proj_rule (i : ι)
  : (fderiv K fun (x : (i : ι) → E i) => x i)
    =
    fun _ => fun dx =>L[K] dx i := 
by 
  funext x; sorry_proof -- somehow use fderiv_pi
variable {E}


theorem fderiv.comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x)
  : (fderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K f y dy
      dz :=
by 
  rw[show (fun x => f (g x)) = f ∘ g by rfl]
  rw[fderiv.comp x hf hg]
  ext dx; simp


theorem fderiv.comp_rule
  (f : Y → Z) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x : X => f (g x))
    =
    fun x => fun dx =>L[K] fderiv K f (g x) (fderiv K g x dx)
         :=
by 
  funext x;
  rw[show (fun x => f (g x)) = f ∘ g by rfl]
  rw[fderiv.comp x (hf (g x)) (hg x)]
  ext dx; simp


theorem fderiv.let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x)) 
  (hg : DifferentiableAt K g x)
  : (fderiv K
      fun x : X =>
        let y := g x
        f x y) x
    =
    let y  := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by
  have h : (fun x => f x (g x)) = (fun xy : X×Y => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  conv => 
    lhs
    rw[h]
    rw[fderiv.comp x hf (DifferentiableAt.prod (by simp) hg)]
    rw[DifferentiableAt.fderiv_prod (by simp) hg]
  ext dx; simp[ContinuousLinearMap.comp]
  rfl


theorem fderiv.let_rule
  (f : X → Y → Z) (g : X → Y) 
  (hf : Differentiable K fun xy : X×Y => f xy.1 xy.2) (hg : Differentiable K g)
  : (fderiv K fun x : X =>
       let y := g x
       f x y)
    =
    fun x => 
      let y  := g x
      fun dx =>L[K]
        let dy := fderiv K g x dx
        let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
        dz := 
by
  funext x
  apply fderiv.let_rule_at _ _ _ x (hf (x,g x)) (hg x)


theorem fderiv.pi_rule_at
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : (fderiv K fun (x : X) (i : ι) => f x i) x
    = 
    fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx
  := fderiv_pi hf


theorem fderiv.pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (fderiv K fun (x : X) (i : ι) => f x i)
    = 
    fun x => fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx
  := by funext x; apply fderiv_pi (fun i => hf i x)

variable {K}



-- Register `fderiv` as function transformation --------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def fderiv.discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    -- if `fprop` fails try assumption
    let tac := FTrans.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption")
    let proof? ← tac e
    return proof?

open Lean Meta FTrans in
def fderiv.ftransExt : FTransExt where
  ftransName := ``fderiv

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
      e.setArg 8  f
    else          
      e

  idRule  e X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false},
         { proof := ← mkAppM ``comp_rule_at #[K, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false},
         { proof := ← mkAppM ``let_rule_at #[K, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false},
         { proof := ← mkAppM ``pi_rule_at #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := fderiv.discharger


-- register fderiv
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fderiv, fderiv.ftransExt))


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



-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.fderiv_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (g x, f x)) x
    =
    fun dx =>L[K]
      (fderiv K g x dx, fderiv K f x dx) := 
by 
  apply DifferentiableAt.fderiv_prod hg hf


@[ftrans]
theorem Prod.mk.arg_fstsnd.fderiv_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Z) (hf : Differentiable K f)
  : fderiv K (fun x => (g x, f x))
    =    
    fun x => fun dx =>L[K]
      (fderiv K g x dx, fderiv K f x dx) := 
by 
  funext x; apply DifferentiableAt.fderiv_prod (hg x) (hf x)

 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.fderiv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (f x).1) x
    =
    fun dx =>L[K] (fderiv K f x dx).1 := 
by
  apply fderiv.fst hf


@[ftrans]
theorem Prod.fst.arg_self.fderiv_rule
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv K (fun x => (f x).1)
    =
    fun x => fun dx =>L[K] (fderiv K f x dx).1 := 
by
  funext x; apply fderiv.fst (hf x)



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.fderiv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => (f x).2) x
    =
    fun dx =>L[K] (fderiv K f x dx).2 := 
by
  apply fderiv.snd hf



@[ftrans]
theorem Prod.snd.arg_self.fderiv_rule
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv K (fun x => (f x).2)
    =
    fun x => fun dx =>L[K] (fderiv K f x dx).2 :=
by
  funext x; apply fderiv.snd (hf x)


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fderiv_rule_at
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv K fun x => f x + g x) x
    =
    fun dx =>L[K]
      fderiv K f x dx + fderiv K g x dx
  := fderiv_add hf hg


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fderiv_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x + g x)
    =
    fun x => fun dx =>L[K]
      fderiv K f x dx + fderiv K g x dx
  := by funext x; apply fderiv_add (hf x) (hg x)



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.fderiv_rule_at
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv K fun x => f x - g x) x
    =
    fun dx =>L[K]
      fderiv K f x dx - fderiv K g x dx
  := fderiv_sub hf hg


@[ftrans]
theorem HSub.hSub.arg_a0a1.fderiv_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x - g x)
    =
    fun x => fun dx =>L[K]
      fderiv K f x dx - fderiv K g x dx
  := by funext x; apply fderiv_sub (hf x) (hg x)



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.fderiv_rule'
  (x : X) (f : X → Y)
  : (fderiv K fun x => - f x) x
    =
    fun dx =>L[K]
      - fderiv K f x dx
  := fderiv_neg


@[ftrans]
theorem Neg.neg.arg_a0.fderiv_rule
  (f : X → Y)
  : (fderiv K fun x => - f x)
    =
    fun x => fun dx =>L[K]
      - fderiv K f x dx
  := by funext x; apply fderiv_neg


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HMul.hMul.arg_a0a1.fderiv_rule_at
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (x : X) (f g : X → Y)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv K fun x => f x * g x) x
    =
    let fx := f x
    let gx := g x
    fun dx =>L[K]
      (fderiv K g x dx) * fx + (fderiv K f x dx) * gx := 
by
  ext dx
  simp[fderiv_mul hf hg, mul_comm]; rfl


@[ftrans]
theorem HMul.hMul.arg_a0a1.fderiv_rule
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (f g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x * g x)
    =
    fun x => 
      let fx := f x
      let gx := g x
      fun dx =>L[K]
        (fderiv K g x dx) * fx + (fderiv K f x dx) * gx := 
by 
  funext x; ext dx;
  simp[fderiv_mul (hf x) (hg x), mul_comm]; rfl



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fderiv_rule_at
  (x : X) (f : X → K) (g : X → Y) 
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>L[K]
      k • (fderiv K g x dx) + (fderiv K f x dx) • y  
  := fderiv_smul hf hg


@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fderiv_rule
  (f : X → K) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv K fun x => f x • g x)
    =
    fun x => 
      let k := f x
      let y := g x
      fun dx =>L[K]
        k • (fderiv K g x dx) + (fderiv K f x dx) • y  
  := by funext x; apply fderiv_smul (hf x) (hg x)



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fderiv_rule_at
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K) 
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : (fderiv R fun x => f x / g x) x
    =
    let k := f x
    let k' := g x
    fun dx =>L[R]
      ((fderiv R f x dx) * k' - k * (fderiv R g x dx)) / k'^2 := 
by
  have h : ∀ (f : R → K) x, fderiv R f x 1 = deriv f x := by simp[deriv]
  ext; simp[h]; apply deriv_div hf hg hx


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fderiv_rule
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (f : R → K) (g : R → K) 
  (hf : Differentiable R f) (hg : Differentiable R g) (hx : ∀ x, g x ≠ 0)
  : (fderiv R fun x => f x / g x)
    =
    fun x => 
      let k := f x
      let k' := g x
      fun dx =>L[R]
        ((fderiv R f x dx) * k' - k * (fderiv R g x dx)) / k'^2 := 
by
  have h : ∀ (f : R → K) x, fderiv R f x 1 = deriv f x := by simp[deriv]
  ext x; simp[h]; apply deriv_div (hf x) (hg x) (hx x)


-- HPow.hPow ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.fderiv_rule_at
  (n : Nat) (x : X) (f : X → K) (hf : DifferentiableAt K f x)
  : fderiv K (fun x => f x ^ n) x
    =
    fun dx =>L[K] n * fderiv K f x dx * (f x ^ (n-1)) :=
by
  induction n
  case zero =>
    simp; rfl
  case succ n hn =>
    ext dx
    simp_rw[pow_succ]
    rw[HMul.hMul.arg_a0a1.fderiv_rule_at x f _ (by fprop) (by fprop)]
    rw[hn]
    induction n
    case zero => simp
    case succ =>
      rw[show ∀ (n : Nat), n.succ - 1 = n by simp]
      rw[pow_succ]
      simp; ring


@[ftrans]
def HPow.hPow.arg_a0.fderiv_rule
  (n : Nat) (f : X → K) (hf : Differentiable K f)
  : fderiv K (fun x => f x ^ n)
    =
    fun x => fun dx =>L[K] n * fderiv K f x dx * (f x ^ (n-1)) :=
by
  funext x; apply HPow.hPow.arg_a0.fderiv_rule_at n x f (hf x)
