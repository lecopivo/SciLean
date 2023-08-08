import SciLean.Core.FunctionPropositions.IsDifferentiable 
import SciLean.Core.FunctionPropositions.IsDifferentiableAt

import SciLean.Tactic.FTrans.Basic

set_option linter.unusedVariables false

namespace SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

noncomputable
def cderiv (K : Type _) [IsROrC K]
  {X Y : Type _} [Vec K X] [Vec K Y]
  (f : X → Y) (x dx : X) : Y := Curve.deriv (fun t : K => f (x + t•dx)) 0

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------
variable (K)
variable (X)
theorem cderiv.id_rule 
  : (cderiv K fun x : X => x) = fun _ => fun dx => dx
  := by sorry_proof
variable {X}

variable (Y)
theorem cderiv.const_rule (x : X)
  : (cderiv K fun _ : Y => x) = fun _ => fun dx => 0
  := by sorry_proof
variable {Y}

variable (E)
theorem cderiv.proj_rule (i : ι)
  : (cderiv K fun (x : (i : ι) → E i) => x i)
    =
    fun _ => fun dx => dx i := 
by sorry_proof
variable {E}


theorem cderiv.comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : IsDifferentiableAt K f (g x)) (hg : IsDifferentiableAt K g x)
  : (cderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>
      let dy := cderiv K g x dx
      let dz := cderiv K f y dy
      dz :=
by sorry_proof


theorem cderiv.comp_rule
  (f : Y → Z) (g : X → Y) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (cderiv K fun x : X => f (g x))
    =
    fun x => 
      let y := g x
      fun dx =>
        let dy := cderiv K g x dx
        let dz := cderiv K f y dy
        dz :=
by sorry_proof


theorem cderiv.let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : IsDifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x)) 
  (hg : IsDifferentiableAt K g x)
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
by sorry_proof


theorem cderiv.let_rule
  (f : X → Y → Z) (g : X → Y) 
  (hf : IsDifferentiable K fun xy : X×Y => f xy.1 xy.2) (hg : IsDifferentiable K g)
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
by sorry_proof


theorem cderiv.pi_rule_at
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, IsDifferentiableAt K (f · i) x)
  : (cderiv K fun (x : X) (i : ι) => f x i) x
    = 
    fun dx => fun i =>
      cderiv K (f · i) x dx
  := by sorry_proof


theorem cderiv.pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsDifferentiable K (f · i))
  : (cderiv K fun (x : X) (i : ι) => f x i)
    = 
    fun x => fun dx => fun i =>
      cderiv K (f · i) x dx
  := by sorry_proof

variable {K}



-- Register `cderiv` as function transformation --------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def cderiv.discharger (e : Expr) : SimpM (Option Expr) := do
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
def cderiv.ftransExt : FTransExt where
  ftransName := ``cderiv

  getFTransFun? e := 
    if e.isAppOf ``cderiv then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``cderiv then
      e.modifyArg (fun _ => f) 6
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

  discharger := cderiv.discharger


-- register cderiv
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``cderiv, cderiv.ftransExt))


end SciLean

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem id.arg_a.cderiv_rule
  : cderiv K (id : X → X) 
    =
    fun _ => id := by unfold id; ftrans


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Function.comp.arg_a0.cderiv_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : IsDifferentiableAt K f (g x)) (hg : IsDifferentiableAt K g x)
  : cderiv K (f ∘ g) x
    =
    fun dx => 
      cderiv K f (g x) (cderiv K g x dx) := 
by 
  unfold Function.comp; ftrans

@[ftrans]
theorem Function.comp.arg_a0.cderiv_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : cderiv K (f ∘ g)
    =
    fun x => cderiv K f (g x) ∘ (cderiv K g x) := 
by 
  unfold Function.comp; ftrans


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.cderiv_rule_at
  (x : X)
  (g : X → Y) (hg : IsDifferentiableAt K g x)
  (f : X → Z) (hf : IsDifferentiableAt K f x)
  : cderiv K (fun x => (g x, f x)) x
    =
    fun dx =>
      (cderiv K g x dx, cderiv K f x dx) := 
by sorry_proof



@[ftrans]
theorem Prod.mk.arg_fstsnd.cderiv_rule
  (g : X → Y) (hg : IsDifferentiable K g)
  (f : X → Z) (hf : IsDifferentiable K f)
  : cderiv K (fun x => (g x, f x))
    =    
    fun x => fun dx =>
      (cderiv K g x dx, cderiv K f x dx) := 
by sorry_proof


 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.cderiv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : IsDifferentiableAt K f x)
  : cderiv K (fun x => (f x).1) x
    =
    fun dx => (cderiv K f x dx).1 := 
by sorry_proof



@[ftrans]
theorem Prod.fst.arg_self.cderiv_rule
  (f : X → Y×Z) (hf : IsDifferentiable K f)
  : cderiv K (fun x => (f x).1)
    =
    fun x => fun dx => (cderiv K f x dx).1 := 
by sorry_proof



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.cderiv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : IsDifferentiableAt K f x)
  : cderiv K (fun x => (f x).2) x
    =
    fun dx => (cderiv K f x dx).2 := 
by sorry_proof


@[ftrans]
theorem Prod.snd.arg_self.cderiv_rule
  (f : X → Y×Z) (hf : IsDifferentiable K f)
  : cderiv K (fun x => (f x).2)
    =
    fun x => fun dx => (cderiv K f x dx).2 :=
by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.cderiv_rule_at
  (x : X) (f g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (cderiv K fun x => f x + g x) x
    =
    fun dx =>
      cderiv K f x dx + cderiv K g x dx
  := by sorry_proof


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.cderiv_rule
  (f g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (cderiv K fun x => f x + g x)
    =
    fun x => fun dx =>
      cderiv K f x dx + cderiv K g x dx
  := by sorry_proof



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.cderiv_rule_at
  (x : X) (f g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (cderiv K fun x => f x - g x) x
    =
    fun dx =>
      cderiv K f x dx - cderiv K g x dx
  := by sorry_proof


@[ftrans]
theorem HSub.hSub.arg_a0a1.cderiv_rule
  (f g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (cderiv K fun x => f x - g x)
    =
    fun x => fun dx =>
      cderiv K f x dx - cderiv K g x dx
  := by sorry_proof



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.cderiv_rule'
  (x : X) (f : X → Y)
  : (cderiv K fun x => - f x) x
    =
    fun dx =>
      - cderiv K f x dx
  := by sorry_proof


@[ftrans]
theorem Neg.neg.arg_a0.cderiv_rule
  (f : X → Y)
  : (cderiv K fun x => - f x)
    =
    fun x => fun dx =>
      - cderiv K f x dx
  := by sorry_proof


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HMul.hMul.arg_a0a1.cderiv_rule_at
  (x : X) (f g : X → K)
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (cderiv K fun x => f x * g x) x
    =
    let fx := f x
    let gx := g x
    fun dx =>
      (cderiv K g x dx) * fx + (cderiv K f x dx) * gx := 
by sorry_proof


@[ftrans]
theorem HMul.hMul.arg_a0a1.cderiv_rule
  (f g : X → K)
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (cderiv K fun x => f x * g x)
    =
    fun x => 
      let fx := f x
      let gx := g x
      fun dx =>
        (cderiv K g x dx) * fx + (cderiv K f x dx) * gx := 
by sorry_proof


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.cderiv_rule_at
  (x : X) (f : X → K) (g : X → Y) 
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (cderiv K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>
      k • (cderiv K g x dx) + (cderiv K f x dx) • y  
  := by sorry_proof


@[ftrans]
theorem HSMul.hSMul.arg_a0a1.cderiv_rule
  (f : X → K) (g : X → Y) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (cderiv K fun x => f x • g x)
    =
    fun x => 
      let k := f x
      let y := g x
      fun dx =>
        k • (cderiv K g x dx) + (cderiv K f x dx) • y  
  := by sorry_proof



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.cderiv_rule_at
  (x : X) (f : X → K) (g : X → K) 
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x) (hx : g x ≠ 0)
  : (cderiv K fun x => f x / g x) x
    =
    let k := f x
    let k' := g x
    fun dx =>
      ((cderiv K f x dx) * k' - k * (cderiv K g x dx)) / k'^2 := 
by sorry_proof


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.cderiv_rule
  (f : X → K) (g : X → K) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g) (hx : ∀ x, g x ≠ 0)
  : (cderiv K fun x => f x / g x)
    =
    fun x => 
      let k := f x
      let k' := g x
      fun dx =>
        ((cderiv K f x dx) * k' - k * (cderiv K g x dx)) / k'^2 := 
by sorry_proof


-- HPow.hPow ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.cderiv_rule_at
  (n : Nat) (x : X) (f : X → K) (hf : IsDifferentiableAt K f x)
  : cderiv K (fun x => f x ^ n) x
    =
    fun dx => n * cderiv K f x dx * (f x ^ (n-1)) :=
by
  induction n
  case zero =>
    simp; ftrans
  case succ n hn =>
    ext dx
    simp_rw[pow_succ]
    rw[HMul.hMul.arg_a0a1.cderiv_rule_at x f _ (by fprop) (by fprop)]
    rw[hn]
    induction n
    case zero => simp
    case succ =>
      rw[show ∀ (n : Nat), n.succ - 1 = n by simp]
      rw[pow_succ]
      simp; ring


@[ftrans]
def HPow.hPow.arg_a0.cderiv_rule
  (n : Nat) (f : X → K) (hf : IsDifferentiable K f)
  : cderiv K (fun x => f x ^ n)
    =
    fun x => fun dx => n * cderiv K f x dx * (f x ^ (n-1)) :=
by
  funext x; apply HPow.hPow.arg_a0.cderiv_rule_at n x f (hf x)
