import SciLean.Core.FunctionTransformations.FDeriv
import SciLean.Core.FunctionTransformations.Adjoint

import SciLean.Profile

namespace SciLean

-- #profile_this_filea
open ContinuousLinearMap

noncomputable
def revDeriv
  (K : Type _) [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, ContinuousLinearMap.adjoint (fderiv K f x))


namespace revDeriv

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]




-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

theorem id_rule 
  : revDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) :=
by
  unfold revDeriv
  funext _
  ftrans; ftrans; ext; simp


theorem const_rule (x : X)
  : revDeriv K (fun _ : Y => x) = fun y => (x, fun _ => 0) :=
by
  unfold revDeriv
  funext _
  ftrans; ftrans; ext; simp


theorem proj_rule [DecidableEq ι] (i : ι)
  : revDeriv K (fun (x : PiLp 2 (fun (_ : ι) => X)) => x i) 
    = 
    fun x => 
      (x i, fun dxi j => if i=j then dxi else (0 : X)) :=
by
  unfold revDeriv
  funext _; ext; dsimp; dsimp
  -- Here we are in trouble because fderiv depends on the norm
  have h : (fderiv K fun (x : PiLp 2 (fun (_ : ι) => X)) => x i) 
           =
           fun _ => fun dx =>L[K] dx i := sorry_proof -- by apply fderiv.proj_rule 
  rw[h]
  dsimp; ftrans only; simp

#check fderiv.proj_rule 

theorem comp_rule 
  (g : X → Y) (hg : Differentiable K g)
  (f : Y → Z) (hf : Differentiable K f)
  : revDeriv K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDeriv K g x
      let zdf := revDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := 
by
  unfold revDeriv
  funext _
  ftrans; ftrans


theorem let_rule 
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Y → Z) (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2))
  : revDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDeriv K g x 
      let zdf := revDeriv K (fun (xy : X×₂Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  :=
by
  unfold revDeriv
  funext x
  conv =>
    lhs
    ftrans only
    ftrans only
    enter [2, y]
    rw[show 
        (fun dx =>
           let dy := fderiv' K (fun x => g x) x dx;
           let dz := fderiv' K (fun xy => f xy.fst xy.snd) (x, y) (dx, dy);
         dz)
        =
        fun dx =>
          let dy := fderiv' K (fun x => g x) x dx;
          let dz := fderiv' K (fun xy : X×₂Y => f xy.fst xy.snd) (x, y) (dx, dy);
        dz
        by funext dx; simp; sorry]
  rw[_root_.SciLean.adjoint'.comp_rule K
     (fderiv' K (fun xy : X×₂Y => f xy.fst xy.snd) (x, g x)) 
     _
     (by fprop) 
     (by fprop)]
  ftrans only
  


open BigOperators in
theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (revDeriv K (Y:= PiLp 2 E) fun (x : X) (i : ι) => f i x)
    =
    fun x =>
      let xdf := fun i =>
        (revDeriv K fun (x : X) => f i x) x
      (fun i => (xdf i).1,
       fun dy => ∑ i, (xdf i).2 (dy i))
       :=
by
  unfold revDeriv
  funext _; simp
  set_option trace.Meta.Tactic.simp.unify true in
  ftrans only
  ftrans
  ext _; simp
  sorry


set_option profiler true in



example
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : DifferentiableAt K f y) (hg : IsContinuousLinearMap K g)
  : IsContinuousLinearMap K (fun dx => fderiv' K f y (g dx)) := by fprop

example
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : Y → Z) (hf : DifferentiableAt K f (g x))
  : let y : Nat := 1 + 1;
    IsContinuousLinearMap K fun dy => fderiv' K (fun x0 => f x0) (g x) dy :=
by
  set_option trace.Meta.Tactic.fprop.discharge true in
  set_option trace.Meta.Tactic.fprop.step true in
  set_option trace.Meta.Tactic.fprop.unify true in
  fprop


example
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : Y → Z) (hf : DifferentiableAt K f (g x))
  : let y := g x;
    DifferentiableAt K (fun x0 => f x0) y :=
by
  intro y
  fprop



theorem comp_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : Y → Z) (hf : DifferentiableAt K f (g x))
  : revDeriv K (fun x : X => f (g x)) x
    = 
    let ydg := revDeriv K g x 
    let zdf := revDeriv K f ydg.1
    (zdf.1,    
     fun dz => 
     ydg.2 (zdf.2 dz)) :=
by
  unfold revDeriv
  simp; ftrans only; ftrans only
  set_option trace.Meta.Tactic.ftrans.discharge true in
  set_option trace.Meta.Tactic.fprop.discharge true in
  ftrans only


#exit

theorem let_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Y → Z) (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x))
  : revDeriv K (fun x : X => let y := g x; f x y) x
    = 
    fun dx => 
      let ydy := revDeriv K g x dx 
      let zdz := revDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold revDeriv
  funext dx;
  rw[fderiv.let_rule_at x g hg f hf]
  simp


theorem pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (revDeriv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx =>
      (fun i => f i x, fun i => (revDeriv K (f i) x dx).2) := 
by 
  unfold revDeriv
  rw[fderiv.pi_rule_at x f hf]
  simp



-- Register `revDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------
#check `(tactic| assumption) 
#check Lean.Syntax

open Lean Meta Qq in
def revDeriv.discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
def revDeriv.ftransExt : FTransExt where
  ftransName := ``revDeriv

  getFTransFun? e := 
    if e.isAppOf ``revDeriv then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDeriv then
      e.modifyArg (fun _ => f) 8
    else          
      e

  idRule    := tryNamedTheorem ``id_rule discharger
  constRule := tryNamedTheorem ``const_rule discharger
  projRule  := tryNamedTheorem ``proj_rule discharger
  compRule  e f g := do
    let .some K := e.getArg? 0
      | return none

    let mut thrms : Array SimpTheorem := #[]

    thrms := thrms.push {
      proof := ← mkAppM ``comp_rule #[K, f, g]
      origin := .decl ``comp_rule
      rfl := false
    }

    thrms := thrms.push {
      proof := ← mkAppM ``comp_rule_at #[K, f, g]
      origin := .decl ``comp_rule
      rfl := false
    }

    for thm in thrms do
      if let some result ← Meta.Simp.tryTheorem? e thm discharger then
        return Simp.Step.visit result
    return none

  letRule e f g := do
    let .some K := e.getArg? 0
      | return none

    let mut thrms : Array SimpTheorem := #[]

    thrms := thrms.push {
      proof := ← mkAppM ``let_rule #[K, f, g]
      origin := .decl ``comp_rule
      rfl := false
    }

    thrms := thrms.push {
      proof := ← mkAppM ``let_rule_at #[K, f, g]
      origin := .decl ``comp_rule
      rfl := false
    }

    for thm in thrms do
      if let some result ← Meta.Simp.tryTheorem? e thm discharger then
        return Simp.Step.visit result
    return none

  piRule  e f := do
    let .some K := e.getArg? 0
      | return none

    let mut thrms : Array SimpTheorem := #[]

    thrms := thrms.push {
      proof := ← mkAppM ``pi_rule #[K, f]
      origin := .decl ``comp_rule
      rfl := false
    }

    thrms := thrms.push {
      proof := ← mkAppM ``pi_rule_at #[K, f]
      origin := .decl ``comp_rule
      rfl := false
    }

    for thm in thrms do
      if let some result ← Meta.Simp.tryTheorem? e thm discharger then
        return Simp.Step.visit result
    return none

  discharger := revDeriv.discharger


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDeriv, revDeriv.ftransExt))


end SciLean.revDeriv

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

@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.revDeriv_at_comp
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Z) (hf : DifferentiableAt K f x)
  : revDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := revDeriv K g x dx
      let zdz := revDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := 
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.revDeriv_comp
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Z) (hf : Differentiable K f)
  : revDeriv K (fun x => (g x, f x))
    =    
    fun x dx =>
      let ydy := revDeriv K g x dx
      let zdz := revDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := 
by 
  unfold revDeriv; ftrans

 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Prod.fst.arg_self.revDeriv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : revDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := revDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := 
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem Prod.fst.arg_self.revDeriv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : revDeriv K (fun x => (f x).1)
    =
    fun x dx =>
      let yzdyz := revDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) :=
by 
  unfold revDeriv; ftrans



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Prod.snd.arg_self.revDeriv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : revDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := revDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem Prod.snd.arg_self.revDeriv_comp
  (f : X → Y×Z) (hf : Differentiable K f)
  : revDeriv K (fun x => (f x).2)
    =
    fun x dx =>
      let yzdyz := revDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold revDeriv; ftrans



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.revDeriv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revDeriv K fun x => f x + g x) x
    =
    fun dx =>
      revDeriv K f x dx + revDeriv K g x dx := 
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.revDeriv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (revDeriv K fun x => f x + g x)
    =
    fun x dx =>
      revDeriv K f x dx + revDeriv K g x dx := 
by 
  unfold revDeriv; ftrans



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HSub.hSub.arg_a4a5.revDeriv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revDeriv K fun x => f x - g x) x
    =
    fun dx =>
      revDeriv K f x dx - revDeriv K g x dx := 
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem HSub.hSub.arg_a4a5.revDeriv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (revDeriv K fun x => f x - g x)
    =
    fun x dx =>
      revDeriv K f x dx - revDeriv K g x dx :=
by 
  unfold revDeriv; ftrans



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Neg.neg.arg_a2.revDeriv_at_comp
  (x : X) (f : X → Y)
  : (revDeriv K fun x => - f x) x
    =
    fun dx => - revDeriv K f x dx :=
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem Neg.neg.arg_a2.revDeriv_comp
  (f : X → Y)
  : (revDeriv K fun x => - f x)
    =
    fun x dx => - revDeriv K f x dx :=
by  
  unfold revDeriv; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HMul.hMul.arg_a4a5.revDeriv_at_comp
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (x : X) (f g : X → Y)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (revDeriv K f x dx)
      let zdz := (revDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) :=
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem HMul.hMul.arg_a4a5.revDeriv_comp
  {Y : Type _} [NormedCommRing Y] [NormedAlgebra K Y] 
  (f g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (revDeriv K fun x => f x * g x)
    =
    fun x dx =>
      let ydy := (revDeriv K f x dx)
      let zdz := (revDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) :=
by 
  unfold revDeriv; ftrans


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem SMul.smul.arg_a3a4.revDeriv_at_comp
  (x : X) (f : X → K) (g : X → Y) 
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revDeriv K fun x => f x • g x) x
    =
    fun dx =>
      let ydy := (revDeriv K f x dx)
      let zdz := (revDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) :=
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem SMul.smul.arg_a3a4.revDeriv_comp
  (f : X → K) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (revDeriv K fun x => f x • g x)
    =
    fun x dx =>
      let ydy := (revDeriv K f x dx)
      let zdz := (revDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) :=
by 
  unfold revDeriv; ftrans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HDiv.hDiv.arg_a4a5.revDeriv_at_comp
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K) 
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : (revDeriv R fun x => f x / g x) x
    =
    fun dx =>
      let ydy := (revDeriv R f x dx)
      let zdz := (revDeriv R g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) :=
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
theorem HDiv.hDiv.arg_a4a5.revDeriv_comp
  {R : Type _} [NontriviallyNormedField R] [NormedAlgebra R K]
  (f : R → K) (g : R → K) 
  (hf : Differentiable R f) (hg : Differentiable R g) (hx : ∀ x, g x ≠ 0)
  : (revDeriv R fun x => f x / g x)
    =
    fun x dx =>
      let ydy := (revDeriv R f x dx)
      let zdz := (revDeriv R g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) :=
by 
  unfold revDeriv; ftrans


-- HPow.hPow ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans_rule]
def HPow.hPow.arg_a4.revDeriv_at_comp
  (n : Nat) (x : X) (f : X → K) (hf : DifferentiableAt K f x) 
  : revDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := revDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold revDeriv; ftrans


@[ftrans_rule]
def HPow.hPow.arg_a4.revDeriv_comp
  (n : Nat) (f : X → K) (hf : Differentiable K f) 
  : revDeriv K (fun x => f x ^ n)
    =
    fun x dx =>
      let ydy := revDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold revDeriv; ftrans
