import SciLean.FTrans.FDeriv.Basic

namespace SciLean


variable 
  {K : Type _} [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]


variable (K)

noncomputable
def fderiv' (f : X → Y) (x dx : X) : Y := fderiv K f x dx

namespace fderiv'

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule 
  : (fderiv' K fun x : X => x) = fun _ => fun dx => dx
  := by simp[fderiv']
variable {X}

variable (Y)
theorem const_rule (x : X)
  : (fderiv' K fun _ : Y => x) = fun _ => fun dx => 0
  := by simp[fderiv']
variable {Y}

variable (E)
theorem proj_rule (i : ι)
  : (fderiv' K fun (x : (i : ι) → E i) => x i)
    =
    fun x => fun dx => dx i := 
by 
  simp[fderiv']; ftrans
variable {E}


theorem comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x)
  : (fderiv' K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>
      let dy := fderiv' K g x dx
      let dz := fderiv' K f y dy
      dz :=
by 
  unfold fderiv'; ftrans


theorem comp_rule
  (f : Y → Z) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv' K fun x : X => f (g x))
    =
    fun x => 
      let y := g x
      fun dx =>
        let dy := fderiv' K g x dx
        let dz := fderiv' K f y dy
        dz :=
by 
  unfold fderiv'; ftrans


theorem let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x)) 
  (hg : DifferentiableAt K g x)
  : (fderiv' K
      fun x : X =>
        let y := g x
        f x y) x
    =
    let y  := g x
    fun dx =>
      let dy := fderiv' K g x dx
      let dz := fderiv' K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz :=
by
  unfold fderiv'; ftrans


theorem let_rule
  (f : X → Y → Z) (g : X → Y) 
  (hf : Differentiable K fun xy : X×Y => f xy.1 xy.2) (hg : Differentiable K g)
  : (fderiv' K fun x : X =>
       let y := g x
       f x y)
    =
    fun x => 
      let y  := g x
      fun dx =>
        let dy := fderiv' K g x dx
        let dz := fderiv' K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
        dz := 
by
  unfold fderiv'; ftrans


theorem pi_rule_at
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : (fderiv' K fun (x : X) (i : ι) => f x i) x
    = 
    fun dx => fun i =>
      fderiv' K (f · i) x dx
  := by unfold fderiv'; ftrans


theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (fderiv' K fun (x : X) (i : ι) => f x i)
    = 
    fun x => fun dx => fun i =>
      fderiv' K (f · i) x dx
  := by unfold fderiv'; ftrans

variable {K}



-- Register `fderiv'` as function transformation --------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
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

open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``fderiv'

  getFTransFun? e := 
    if e.isAppOf ``fderiv' then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fderiv' then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  idRule  e X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false } ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, y], origin := .decl ``const_rule, rfl := false } ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X, i], origin := .decl ``proj_rule, rfl := false } ]
      discharger e

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false },
         { proof := ← mkAppM ``comp_rule_at #[K, f, g], origin := .decl ``comp_rule, rfl := false } ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false },
         { proof := ← mkAppM ``let_rule_at #[K, f, g], origin := .decl ``let_rule, rfl := false } ]
      discharger e

  piRule  e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false },
         { proof := ← mkAppM ``pi_rule_at #[K, f], origin := .decl ``pi_rule, rfl := false } ]
      discharger e

  discharger := discharger


-- register fderiv'
open Lean in
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fderiv', ftransExt))


end SciLean.fderiv'

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


-- fderiv' ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem SciLean.fderiv'.arg_dx.IsContinuousLinearMap_rule
  (f : Y → Z) (g : X → Y) (y : Y)
  (hg : IsContinuousLinearMap K g)
  : IsContinuousLinearMap K (fun dx => fderiv' K f y (g dx)) := by unfold fderiv'; fprop


@[fprop]
theorem SciLean.fderiv'.arg_dx.IsContinuousLinearMap_rule_at
  (f : Y → Z) (g : X → Y) (y : Y)
  (hg : IsContinuousLinearMap K g)
  : IsContinuousLinearMap K (fun dx => fderiv' K f y (g dx)) := by unfold fderiv'; fprop


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.fderiv'_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Z) (hf : DifferentiableAt K f x)
  : fderiv' K (fun x => (g x, f x)) x
    =
    fun dx =>
      (fderiv' K g x dx, fderiv' K f x dx) := 
by 
  unfold fderiv'; ftrans


@[ftrans]
theorem Prod.mk.arg_fstsnd.fderiv'_rule
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Z) (hf : Differentiable K f)
  : fderiv' K (fun x => (g x, f x))
    =    
    fun x => fun dx =>
      (fderiv' K g x dx, fderiv' K f x dx) := 
by 
  unfold fderiv'; ftrans


 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.fderiv'_rule_at
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv' K (fun x => (f x).1) x
    =
    fun dx => (fderiv' K f x dx).1 := 
by 
  unfold fderiv'; ftrans


@[ftrans]
theorem Prod.fst.arg_self.fderiv'_rule
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv' K (fun x => (f x).1)
    =
    fun x => fun dx => (fderiv' K f x dx).1 := 
by
  unfold fderiv'; ftrans



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.fderiv'_rule_at
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fderiv' K (fun x => (f x).2) x
    =
    fun dx => (fderiv' K f x dx).2 := 
by
  unfold fderiv'; ftrans



@[ftrans]
theorem Prod.snd.arg_self.fderiv'_rule
  (f : X → Y×Z) (hf : Differentiable K f)
  : fderiv' K (fun x => (f x).2)
    =
    fun x => fun dx => (fderiv' K f x dx).2 :=
by
  unfold fderiv'; ftrans



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fderiv'_rule_at
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv' K fun x => f x + g x) x
    =
    fun dx =>
      fderiv' K f x dx + fderiv' K g x dx := 
by
  unfold fderiv'; ftrans


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fderiv'_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv' K fun x => f x + g x)
    =
    fun x => fun dx =>
      fderiv' K f x dx + fderiv' K g x dx := 
by 
  unfold fderiv'; ftrans



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.fderiv'_rule_at
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv' K fun x => f x - g x) x
    =
    fun dx =>
      fderiv' K f x dx - fderiv' K g x dx :=
by
  unfold fderiv'; ftrans


@[ftrans]
theorem HSub.hSub.arg_a0a1.fderiv'_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv' K fun x => f x - g x)
    =
    fun x => fun dx =>
      fderiv' K f x dx - fderiv' K g x dx := 
by
  unfold fderiv'; ftrans



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.fderiv'_rule'
  (x : X) (f : X → Y)
  : (fderiv' K fun x => - f x) x
    =
    fun dx =>
      - fderiv' K f x dx :=
by
  unfold fderiv'; ftrans


@[ftrans]
theorem Neg.neg.arg_a0.fderiv'_rule
  (f : X → Y)
  : (fderiv' K fun x => - f x)
    =
    fun x => fun dx =>
      - fderiv' K f x dx :=
by
  unfold fderiv'; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HMul.hMul.arg_a0a1.fderiv'_rule_at
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (x : X) (f g : X → Y)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv' K fun x => f x * g x) x
    =
    let fx := f x
    let gx := g x
    fun dx =>
      (fderiv' K g x dx) * fx + (fderiv' K f x dx) * gx := 
by
  unfold fderiv'; ftrans


@[ftrans]
theorem HMul.hMul.arg_a0a1.fderiv'_rule
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (f g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv' K fun x => f x * g x)
    =
    fun x => 
      let fx := f x
      let gx := g x
      fun dx =>
        (fderiv' K g x dx) * fx + (fderiv' K f x dx) * gx := 
by 
  unfold fderiv'; ftrans



-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fderiv'_rule_at
  (x : X) (f : X → K) (g : X → Y) 
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fderiv' K fun x => f x • g x) x
    =
    let k := f x
    let y := g x
    fun dx =>
      k • (fderiv' K g x dx) + (fderiv' K f x dx) • y :=
by
  unfold fderiv'; ftrans


@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fderiv'_rule
  (f : X → K) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (fderiv' K fun x => f x • g x)
    =
    fun x => 
      let k := f x
      let y := g x
      fun dx =>
        k • (fderiv' K g x dx) + (fderiv' K f x dx) • y := 
by 
  unfold fderiv'; ftrans



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fderiv'_rule_at
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K) 
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : (fderiv' R fun x => f x / g x) x
    =
    let k := f x
    let k' := g x
    fun dx =>
      ((fderiv' R f x dx) * k' - k * (fderiv' R g x dx)) / k'^2 := 
by
  unfold fderiv'; ftrans


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fderiv'_rule
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (f : R → K) (g : R → K) 
  (hf : Differentiable R f) (hg : Differentiable R g) (hx : ∀ x, g x ≠ 0)
  : (fderiv' R fun x => f x / g x)
    =
    fun x => 
      let k := f x
      let k' := g x
      fun dx =>
        ((fderiv' R f x dx) * k' - k * (fderiv' R g x dx)) / k'^2 := 
by
  unfold fderiv'; ftrans


-- HPow.hPow ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.fderiv'_rule_at
  (n : Nat) (x : X) (f : X → K) (hf : DifferentiableAt K f x)
  : fderiv' K (fun x => f x ^ n) x
    =
    fun dx => n * fderiv' K f x dx * (f x ^ (n-1)) :=
by
  unfold fderiv'; ftrans


@[ftrans]
def HPow.hPow.arg_a0.fderiv'_rule
  (n : Nat) (f : X → K) (hf : Differentiable K f)
  : fderiv' K (fun x => f x ^ n)
    =
    fun x => fun dx => n * fderiv' K f x dx * (f x ^ (n-1)) :=
by
  unfold fderiv'; ftrans
