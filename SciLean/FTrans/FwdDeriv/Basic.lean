import SciLean.FTrans.FDeriv.Basic
import SciLean.Profile

namespace SciLean

noncomputable
def fwdDeriv
  (K : Type _) [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  (f : X → Y) (x dx : X) : Y×Y :=
  (f x, fderiv K f x dx)


namespace fwdDeriv

variable
  {K : Type _} [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace K (E j)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (K)

variable (X)
theorem id_rule 
  : fwdDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdDeriv; ftrans
variable {X}

variable (Y)
theorem const_rule (x : X)
  : fwdDeriv K (fun _ : Y => x) = fun y dy => (x, 0) :=
by
  unfold fwdDeriv; ftrans
variable {Y}

variable (E)
theorem proj_rule (i : ι)
  : fwdDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) :=
by
  unfold fwdDeriv; ftrans
variable {E}


theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : fwdDeriv K (fun x : X => f (g x)) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdDeriv; ftrans


theorem let_rule 
  (f : X → Y → Z) (g : X → Y)
  (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g)
  : fwdDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdDeriv; ftrans


theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (fwdDeriv K fun (x : X) (i : ι) => f x i)
    = 
    fun x dx =>
      (fun i => f x i, fun i => (fwdDeriv K (f · i) x dx).2) := 
by 
  unfold fwdDeriv; ftrans


theorem comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x)
  : fwdDeriv K (fun x : X => f (g x)) x
    = 
    fun dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdDeriv; ftrans


theorem let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)  
  (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x)) (hg : DifferentiableAt K g x)
  : fwdDeriv K (fun x : X => let y := g x; f x y) x
    = 
    fun dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdDeriv; ftrans


theorem pi_rule_at  
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : (fwdDeriv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      (fun i => f x i, fun i => (fwdDeriv K (f · i) x dx).2) := 
by 
  unfold fwdDeriv; ftrans



-- Register `fwdDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

def discharger (e : Expr) : SimpM (Option Expr) := do
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


open Lean Elab Term FTrans
def ftransExt : FTransExt where
  ftransName := ``fwdDeriv

  getFTransFun? e := 
    if e.isAppOf ``fwdDeriv then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fwdDeriv then
      e.modifyArg (fun _ => f) 8
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
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdDeriv, ftransExt))


end SciLean.fwdDeriv

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

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
theorem Prod.mk.arg_fstsnd.fwdDeriv_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Z) (hf : DifferentiableAt K f x)
  : fwdDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := 
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem Prod.mk.arg_fstsnd.fwdDeriv_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Z) (hf : Differentiable K f)
  : fwdDeriv K (fun x => (g x, f x))
    =    
    fun x dx =>
      let ydy := fwdDeriv K g x dx
      let zdz := fwdDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := 
by 
  unfold fwdDeriv; ftrans

 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.fwdDeriv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fwdDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := 
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem Prod.fst.arg_self.fwdDeriv_rule
  (f : X → Y×Z) (hf : Differentiable K f)
  : fwdDeriv K (fun x => (f x).1)
    =
    fun x dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) :=
by 
  unfold fwdDeriv; ftrans



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.fwdDeriv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fwdDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem Prod.snd.arg_self.fwdDeriv_rule
  (f : X → Y×Z) (hf : Differentiable K f)
  : fwdDeriv K (fun x => (f x).2)
    =
    fun x dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold fwdDeriv; ftrans



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fwdDeriv_rule_at
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fwdDeriv K fun x => f x + g x) x
    =
    fun dx =>
      fwdDeriv K f x dx + fwdDeriv K g x dx := 
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fwdDeriv_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K fun x => f x + g x)
    =
    fun x dx =>
      fwdDeriv K f x dx + fwdDeriv K g x dx := 
by 
  unfold fwdDeriv; ftrans



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.fwdDeriv_rule_at
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fwdDeriv K fun x => f x - g x) x
    =
    fun dx =>
      fwdDeriv K f x dx - fwdDeriv K g x dx := 
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem HSub.hSub.arg_a0a1.fwdDeriv_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K fun x => f x - g x)
    =
    fun x dx =>
      fwdDeriv K f x dx - fwdDeriv K g x dx :=
by 
  unfold fwdDeriv; ftrans



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.fwdDeriv_rule_at
  (x : X) (f : X → Y)
  : (fwdDeriv K fun x => - f x) x
    =
    fun dx => - fwdDeriv K f x dx :=
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem Neg.neg.arg_a0.fwdDeriv_rule
  (f : X → Y)
  : (fwdDeriv K fun x => - f x)
    =
    fun x dx => - fwdDeriv K f x dx :=
by  
  unfold fwdDeriv; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HMul.hMul.arg_a0a1.fwdDeriv_rule_at
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (x : X) (f g : X → Y)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fwdDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) :=
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem HMul.hMul.arg_a0a1.fwdDeriv_rule
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (f g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K fun x => f x * g x)
    =
    fun x dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) :=
by 
  unfold fwdDeriv; ftrans


-- HSMul.hSMul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fwdDeriv_rule_at
  (x : X) (f : X → K) (g : X → Y) 
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fwdDeriv K fun x => f x • g x) x
    =
    fun dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) :=
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fwdDeriv_rule
  (f : X → K) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K fun x => f x • g x)
    =
    fun x dx =>
      let ydy := (fwdDeriv K f x dx)
      let zdz := (fwdDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) :=
by 
  unfold fwdDeriv; ftrans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fwdDeriv_rule_at
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K) 
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : (fwdDeriv R fun x => f x / g x) x
    =
    fun dx =>
      let ydy := (fwdDeriv R f x dx)
      let zdz := (fwdDeriv R g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) :=
by 
  unfold fwdDeriv; ftrans


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fwdDeriv_rule
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (f : R → K) (g : R → K) 
  (hf : Differentiable R f) (hg : Differentiable R g) (hx : ∀ x, g x ≠ 0)
  : (fwdDeriv R fun x => f x / g x)
    =
    fun x dx =>
      let ydy := (fwdDeriv R f x dx)
      let zdz := (fwdDeriv R g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) :=
by 
  unfold fwdDeriv; ftrans


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.fwdDeriv_rule_at
  (n : Nat) (x : X) (f : X → K) (hf : DifferentiableAt K f x) 
  : fwdDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := fwdDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold fwdDeriv; ftrans


@[ftrans]
def HPow.hPow.arg_a0.fwdDeriv_rule
  (n : Nat) (f : X → K) (hf : Differentiable K f) 
  : fwdDeriv K (fun x => f x ^ n)
    =
    fun x dx =>
      let ydy := fwdDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold fwdDeriv; ftrans
