import SciLean.Core.FunctionPropositions.HasAdjDiffAt
import SciLean.Core.FunctionPropositions.HasAdjDiff

import SciLean.Core.FunctionTransformations.SemiAdjoint

import SciLean.Data.EnumType
  
import SciLean.Util.Profile

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


noncomputable
def revCDeriv
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, semiAdjoint K (cderiv K f x))

--@[ftrans_unfold]
noncomputable
def revCDerivEval
  (f : X → Y) (x : X) (dy : Y) : Y×X :=
  let ydf := revCDeriv K f x
  (ydf.1, ydf.2 dy)

--@[ftrans_unfold]
noncomputable 
def gradient
  (f : X → Y) (x : X) : Y→X := (revCDeriv K f x).2

--@[ftrans_unfold]
noncomputable 
def scalarGradient
  (f : X → K) (x : X) : X := (revCDeriv K f x).2 1

namespace revCDeriv



-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

-- this one is dangerous as it can be applied to rhs again with g = fun x => x
-- we need ftrans guard or something like that
theorem _root_.SciLean.cderiv.arg_dx.semiAdjoint_rule
  (f : Y → Z) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun dx => cderiv K f y (g dx))
    =
    fun dz => 
      semiAdjoint K g (semiAdjoint K (cderiv K f y) dz) := 
by
  apply semiAdjoint.comp_rule K (cderiv K f y) g (hf.2 y) hg

theorem _root_.SciLean.cderiv.arg_dx.semiAdjoint_rule_at
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : HasAdjDiffAt K f y) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun dx => cderiv K f y (g dx))
    =
    fun dz => 
      semiAdjoint K g (semiAdjoint K (cderiv K f y) dz) := 
by
  apply semiAdjoint.comp_rule K (cderiv K f y) g hf.2 hg


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule 
  : revCDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) :=
by
  unfold revCDeriv
  funext _; ftrans; ftrans


theorem const_rule (y : Y)
  : revCDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) :=
by
  unfold revCDeriv
  funext _; ftrans; ftrans
variable{X}

variable(E)
theorem proj_rule [DecidableEq ι] (i : ι)
  : revCDeriv K (fun (x : (i:ι) → E i) => x i)
    = 
    fun x => 
      (x i, fun dxi j => if h : i=j then h ▸ dxi else 0) :=
by
  unfold revCDeriv
  funext _; ftrans; ftrans
variable {E}


theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revCDeriv K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv
  funext _; ftrans; ftrans


theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revCDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv
  funext _; ftrans; ftrans 


open BigOperators in
theorem pi_rule
  (f :  X → (i : ι) → E i) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revCDeriv K fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let xdf := fun i =>
        (revCDeriv K fun (x : X) => f x i) x
      (fun i => (xdf i).1,
       fun dy => ∑ i, (xdf i).2 (dy i))
       :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revCDeriv
  funext _; ftrans; ftrans 


theorem comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt K f (g x)) (hg : HasAdjDiffAt K g x)
  : revCDeriv K (fun x : X => f (g x)) x
    = 
    let ydg := revCDeriv K g x
    let zdf := revCDeriv K f ydg.1
    (zdf.1,
     fun dz =>
       let dy := zdf.2 dz
       ydg.2 dy)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; ftrans; simp
  rw[cderiv.arg_dx.semiAdjoint_rule_at K f (cderiv K g x) (g x) (by fprop) (by fprop)]


theorem let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x)) (hg : HasAdjDiffAt K g x)
  : revCDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv
  funext _; simp; sorry_proof


open BigOperators in
theorem pi_rule_at
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, HasAdjDiffAt K (f · i) x)
  : (revCDeriv K fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let xdf := fun i =>
        (revCDeriv K fun (x : X) => f x i) x
      (fun i => (xdf i).1,
       fun dy => ∑ i, (xdf i).2 (dy i))
       :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revCDeriv
  funext _; ftrans; ftrans 
  sorry_proof



-- Register `revCDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revCDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``revCDeriv

  getFTransFun? e := 
    if e.isAppOf ``revCDeriv then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revCDeriv then
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

  discharger := discharger


-- register revCDeriv
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revCDeriv, ftransExt))

end revCDeriv

end SciLean

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------b

open SciLean 

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.revCDeriv_rule_at
  (g : X → Y) (f : X → Z) (x : X)
  (hg : HasAdjDiffAt K g x) (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => (g x, f x)) x
    =
    let ydg := revCDeriv K g x
    let zdf := revCDeriv K f x
    ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem Prod.mk.arg_fstsnd.revCDeriv_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K f x
      ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp
 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.revCDeriv_rule_at
  (f : X → Y×Z) (x : X) (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => (f x).1) x
    =
    let yzdf := revCDeriv K f x
    (yzdf.1.1, fun dy => yzdf.2 (dy,0)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem Prod.fst.arg_self.revCDeriv_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (f x).1)
    =
    fun x => 
      let yzdf := revCDeriv K f x
      (yzdf.1.1, fun dy => yzdf.2 (dy,0)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.revCDeriv_rule_at
  (f : X → Y×Z) (x : X) (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => (f x).2) x
    =
    let yzdf := revCDeriv K f x
    (yzdf.1.2, fun dz => yzdf.2 (0,dz)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; simp; ftrans; ftrans; simp

@[ftrans]
theorem Prod.snd.arg_self.revCDeriv_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (f x).2)
    =
    fun x => 
      let yzdf := revCDeriv K f x
      (yzdf.1.2, fun dz => yzdf.2 (0,dz)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Function.comp.arg_fga0.revCDeriv_rule 
  (f : W → Y → Z) (g : W → X → Y) (a0 : W → X)
  (hf : HasAdjDiff K (fun wy : W×Y => f wy.1 wy.2))
  (hg : HasAdjDiff K (fun wx : W×X => g wx.1 wx.2))
  (ha0 : HasAdjDiff K a0)
  : revCDeriv K (fun w => ((f w) ∘ (g w)) (a0 w))
    =
    fun w => 
      let xda0 := revCDeriv K a0 w
      let ydg := revCDeriv K (fun wx : W×X => g wx.1 wx.2) (w,xda0.1)
      let zdf := revCDeriv K (fun wy : W×Y => f wy.1 wy.2) (w,ydg.1)
      (zdf.1, 
       fun dz => 
         let dwy := zdf.2 dz
         let dwx := ydg.2 dwy.2
         let dw  := xda0.2 dwx.2
         dwy.1 + dwx.1 + dw):= 

by 
  unfold Function.comp; ftrans; simp[add_assoc]


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revCDeriv_rule_at
  (f g : X → Y) (x : X) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x + g x) x
    =
    let ydf := revCDeriv K f x
    let ydg := revCDeriv K g x
    (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revCDeriv_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x + g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let ydg := revCDeriv K g x
      (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.revCDeriv_rule_at
  (f g : X → Y) (x : X) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x - g x) x
    =
    let ydf := revCDeriv K f x
    let ydg := revCDeriv K g x
    (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem HSub.hSub.arg_a0a1.revCDeriv_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x - g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let ydg := revCDeriv K g x
      (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revCDeriv_rule
  (f : X → Y) (x : X) 
  : (revCDeriv K fun x => - f x) x
    =
    let ydf := revCDeriv K f x
    (-ydf.1, fun dy => - ydf.2 dy) :=
by 
  unfold revCDeriv; simp; ftrans; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[ftrans]
theorem HMul.hMul.arg_a0a1.revCDeriv_rule_at
  (f g : X → K) (x : X)
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x * g x) x
    =
    let ydf := revCDeriv K f x
    let zdg := revCDeriv K g x
    (ydf.1 * zdg.1, fun dx' =>  conj ydf.1 • zdg.2 dx' + conj zdg.1 • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp

@[ftrans]
theorem HMul.hMul.arg_a0a1.revCDeriv_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x * g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revCDeriv K g x
      (ydf.1 * zdg.1, fun dx' => conj ydf.1 • zdg.2 dx' + conj zdg.1 • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revCDeriv_rule_at
  (f : X → K) (g : X → Y) (x : X) 
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x • g x) x
    =
    let ydf := revCDeriv K f x
    let zdg := revCDeriv K g x
    (ydf.1 • zdg.1, fun dx' => ydf.2 (inner dx' zdg.1) + ydf.1 • zdg.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp; sorry_proof


example 
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → K) (g : X → Y) (x : X)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  (hf' : HasSemiAdjoint K f)
  -- : HasSemiAdjoint K fun x_1 => SciLean.cderiv K f x x_1 • g x
  : HasSemiAdjoint K fun dx : X => f dx • g x
  := by fprop

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revCDeriv_rule
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x • g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revCDeriv K g x
      (ydf.1 • zdg.1, fun dx' => conj ydf.1 • zdg.2 dx' + ydf.2 (inner zdg.1 dx')) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revCDeriv_rule_at
  (f g : X → K) (x : X)
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) (hx : g x ≠ 0)
  : (revCDeriv K fun x => f x / g x) x
    =
    let ydf := revCDeriv K f x
    let zdg := revCDeriv K g x
    (ydf.1 / zdg.1, 
     fun dx' => (1 / (conj zdg.1)^2) • (conj zdg.1 • ydf.2 dx' - conj ydf.1 • zdg.2 dx')) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revCDeriv_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0)
  : (revCDeriv K fun x => f x / g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revCDeriv K g x
      (ydf.1 / zdg.1, 
       fun dx' => (1 / (conj zdg.1)^2) • (conj zdg.1 • ydf.2 dx' - conj ydf.1 • zdg.2 dx')) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.revCDeriv_rule_at
  (f : X → K) (x : X) (n : Nat) (hf : HasAdjDiffAt K f x) 
  : revCDeriv K (fun x => f x ^ n) x
    =
    let ydf := revCDeriv K f x
    (ydf.1 ^ n, fun dx' => (n * conj ydf.1 ^ (n-1)) • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; simp; funext dx; ftrans; ftrans; simp[smul_smul]; ring_nf

@[ftrans]
def HPow.hPow.arg_a0.revCDeriv_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revCDeriv K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revCDeriv K f x
      (ydf.1 ^ n, fun dx' => (n * (conj ydf.1 ^ (n-1))) • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  funext x
  unfold revCDeriv; simp; funext dx; ftrans; ftrans; simp[smul_smul]; ring_nf


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

open BigOperators in
@[ftrans]
theorem Finset.sum.arg_f.revCDeriv_rule {ι : Type _} [Fintype ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revCDeriv K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := revCDeriv K (fun x i => f x i) x
      (∑ i, ydf.1 i, 
       fun dy => ydf.2 (fun _ => dy)) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  simp [revCDeriv]
  funext x; simp
  ftrans
  sorry_proof


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revCDeriv_rule {ι : Type _} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revCDeriv K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := revCDeriv K (fun x i => f x i) x
      (∑ i, ydf.1 i, 
       fun dy => ydf.2 (fun _ => dy)) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  simp [revCDeriv]
  funext x; simp
  ftrans
  sorry_proof



--------------------------------------------------------------------------------

section InnerProductSpace

variable 
  {R : Type _} [RealScalar R]
  -- {K : Type _} [Scalar R K]
  {X : Type _} [SemiInnerProductSpace R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[ftrans]
theorem Inner.inner.arg_a0a1.revCDeriv_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revCDeriv R fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revCDeriv R f x
      let y₂dg := revCDeriv R g x
      let dx₁ := y₁df.2 y₂dg.1
      let dx₂ := y₂dg.2 y₁df.1
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr => 
         conj dr • dx₁ + dr • dx₂):=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  simp[revCDeriv]
  funext x; simp
  ftrans only
  simp
  ftrans


@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revCDeriv_rule
  (f : X → Y)
  (hf : HasAdjDiff R f) 
  : (revCDeriv R fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revCDeriv R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr => 
         ((2:R) * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revCDeriv]
  ftrans only
  simp
  ftrans
  simp[smul_smul]


@[ftrans]
theorem SciLean.norm₂.arg_x.revCDeriv_rule_at
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revCDeriv R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revCDeriv R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr => 
       (ynorm⁻¹ * dr) • ydf.2 ydf.1):=
by 
  have ⟨_,_⟩ := hf
  simp[revCDeriv]
  ftrans only
  simp
  ftrans
  funext dr; simp[smul_smul]

end InnerProductSpace

#exit
#eval 0


open BigOperators 
theorem prod_rule_rec
  (f : X×Y → X → Y → Z) (hf : HasAdjDiff K fun x : (X×Y)×X×Y => f x.1 x.2.1 x.2.2)
  : (revCDeriv K fun (xy : X×Y) => f xy xy.1 xy.2)
    =
    fun x =>
      let zdf := revCDeriv K (fun x : (X×Y)×X×Y => f x.1 x.2.1 x.2.2) (x,x.1,x.2)
      (zdf.1, fun dz =>
        let dx := zdf.2 dz
        dx.1 + (dx.2.1, dx.2.2))
       :=
by
  ftrans; simp

#eval 0

theorem hohoho (f : ι → X → Y) (hf : ∀ i, HasSemiAdjoint K (f i)) 
  : semiAdjoint K (fun (x : ι → X) => ∑ i, f i (x i))
    =
    fun y i => semiAdjoint K (f i) y
  := sorry


open BigOperators
example (A : Fin n → Fin m → K) 
  : (semiAdjoint K fun (x : Fin m → K) i => ∑ j, A i j * x j)
    =
    0 := 
by
  rw[semiAdjoint.pi_rule K (E:=fun _ => K) (fun (x : Fin m → K) (i : Fin n) => ∑ j, A i j * x j) (by fprop)]
  conv =>
    lhs
    enter [x,2,i]
    rw[hohoho _ (by fprop)]
    --rw[Finset.sum.arg_f.semiAdjoint_rule K _ (by fprop)]
  ftrans
  simp
  sorry



example
  (f : X×Y → X → Y → Z) (hf : HasAdjDiff K fun x : (X×Y)×X×Y => f x.1 x.2.1 x.2.2)
  : (revCDeriv K fun (xy : X×Y) => f xy xy.1 xy.2)
    =
    fun x =>
      let zdf := revCDeriv K (fun x : (X×Y)×X×Y => f x.1 x.2.1 x.2.2) (x,x.1,x.2)
      (zdf.1, fun dz =>
        let dx := zdf.2 dz
        dx.1 + (dx.2.1, dx.2.2))
       :=
by
  conv => 
    simp
    simp[prod_rule_rec]
    simp[prod_rule_rec]
  ftrans; ftrans; simp


section asdfasdf

variable 
  {K : Type} [IsROrC K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]


open BigOperators in
theorem pi_rule_rec
  (f : (ι → X) → X → Y) (hf : HasAdjDiff K fun x : (ι→X)×X => f x.1 x.2)
  : (revCDeriv K (fun (x : (ι→X)) (i:ι) => f x (x i)))
    =
    fun x =>
      let zdf := fun i => revCDeriv K (fun (x : (ι→X)×X) => f x.1 x.2) (x,x i)
      (fun i => (zdf i).1,
       fun y i => (∑ j, ((zdf j).2 (y j)).1 i) + ((zdf i).2 (y i)).2) :=
by
  have h := revCDeriv.pi_rule K (E:=fun _ => Y) (fun (i : ι) (x : ι → X) => f x (x i))
  rw[h]
  have ⟨_,_⟩ := hf
  ftrans
  simp[revCDeriv]; funext x; simp
  congr 
  funext y i
  simp 
  sorry

