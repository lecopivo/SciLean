import SciLean.Core.FunctionTransformations.RevCDeriv

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


noncomputable
def revDerivUpdate
  (f : X → Y) (x : X) : Y×(Y→X→X) :=
  let ydf := revCDeriv K f x
  (ydf.1, fun dy dx => dx + ydf.2 dy)

-- @[fprop]
-- theorem asdf (f : X → Y) (x : X) (k : K) (hf : HasAdjDiff K f)
--   : HasSemiAdjoint K (fun y => (revDerivUpdate K f x).2 y k 0) := by unfold revDerivUpdate; ftrans; fprop

@[simp, ftrans_simp]
theorem revDerivProj_fst (f : X → Y) (x : X)
  : (revDerivUpdate K f x).1 = f x :=
by
  rfl


namespace revDerivUpdate


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule
  : revDerivUpdate K (fun x : X => x) = fun x => (x, fun dx' dx => dx + dx') :=
by
  unfold revDerivUpdate
  funext _; ftrans


theorem const_rule (y : Y)
  : revDerivUpdate K (fun _ : X => y) = fun x => (y, fun _ dx => dx) :=
by
  unfold revDerivUpdate
  funext _; ftrans
variable {X}

variable (E)
theorem proj_rule (i : ι)
  : revDerivUpdate K (fun (x : (i:ι) → E i) => x i)
    = 
    fun x => 
      (x i, fun dxi dx j => if h : i=j then dx j + h ▸ dxi else dx j) :=
by
  unfold revDerivUpdate
  funext _; ftrans; ftrans; 
  simp; funext dxi dx j; simp; sorry_proof
variable {E}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revCDeriv K f ydg.1
      (zdf.1,
       fun dz dx =>
         let dy := zdf.2 dz
         ydg.2 dy dx)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext _; ftrans; ftrans; simp


theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz dx => 
         let dxdy := zdf.2 dz (dx, 0)
         let dx := ydg.2 dxdy.2 dxdy.1
         dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext x; ftrans; ftrans; simp 
  funext dz dx
  simp[add_assoc]


@[inline] 
def fun_fold {ι : Type _} [EnumType ι] (f : ι → X → X) (x₀ : X) : X := Id.run do
  let mut x := x₀
  for i in fullRange ι do
    x := f i x
  x

theorem pi_rule
  (f :  X → (i : ι) → E i) (hf : ∀ i, HasAdjDiff K (f · i))
  : (revDerivUpdate K fun (x : X) (i : ι) => f x i)
    =
    fun x =>
      let xdf := fun i =>
        (revDerivUpdate K fun (x : X) => f x i) x
      (fun i => (xdf i).1,
       fun dy dx => fun_fold (fun i => (xdf i).2 (dy i)) dx)
       :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revDerivUpdate
  funext _; ftrans; ftrans; simp
  sorry_proof


-- Register `revDerivUpdate` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revDerivUpdate_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``revDerivUpdate

  getFTransFun? e := 
    if e.isAppOf ``revDerivUpdate then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revDerivUpdate then
      e.setArg 6 f
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
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register revDerivUpdate
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revDerivUpdate, ftransExt))

end revDerivUpdate

end SciLean

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean 

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.revDerivUpdate_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K f x
      ((ydg.1,zdf.1), fun dyz dx => zdf.2 dyz.2 (ydg.2 dyz.1 dx)) := 
by 
  unfold revDerivUpdate; ftrans; simp[add_assoc]

 
theorem Prod.mk.arg_fstsnd.revDerivUpdate_rule_simple
  : revDerivUpdate K (fun xy : X × Y => (xy.1, xy.2))
    =
    fun xy => 
      (xy, fun (dx',dy') (dx,dy) => (dx+dx', dy+dy')) := 
by 
  unfold revDerivUpdate; 
  ftrans; simp; rfl


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.revDerivUpdate_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x).1)
    =
    fun x => 
      let yzdf := revDerivUpdate K f x
      (yzdf.1.1, fun dy dx => yzdf.2 (dy,0) dx) := 
by 
  unfold revDerivUpdate; 
  ftrans


theorem Prod.fst.arg_self.revDerivUpdate_rule_simple
  : revDerivUpdate K (fun xy : X×Y => xy.1)
    =
    fun xy => 
      (xy.1, fun dx' (dx,dy) => (dx+dx', dy)) := 
by 
  unfold revDerivUpdate; 
  ftrans; funext x; simp;funext dy (dx₁,dx₂); simp



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.revDerivUpdate_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x).2)
    =
    fun x => 
      let yzdf := revDerivUpdate K f x
      (yzdf.1.2, fun dz dx => yzdf.2 (0,dz) dx) := 
by 
  have ⟨_,_⟩ := hf
  unfold revDerivUpdate; ftrans; ftrans; simp

theorem Prod.snd.arg_self.revDerivUpdate_simple_rule
  : revDerivUpdate K (fun xy : X×Y => xy.2)
    =
    fun xy => 
      (xy.2, fun dy' (dx,dy) => (dx, dy + dy')) := 
by 
  unfold revDerivUpdate; 
  ftrans; funext x; simp;funext dy (dx₁,dx₂); simp


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

-- @[ftrans]
-- theorem Function.comp.arg_fga0.revDerivUpdate_rule 
--   (f : W → Y → Z) (g : W → X → Y) (a0 : W → X)
--   (hf : HasAdjDiff K (fun wy : W×Y => f wy.1 wy.2))
--   (hg : HasAdjDiff K (fun wx : W×X => g wx.1 wx.2))
--   (ha0 : HasAdjDiff K a0)
--   : revDerivUpdate K (fun w => ((f w) ∘ (g w)) (a0 w))
--     =
--     fun w => 
--       let xda0 := revDerivUpdate K a0 w
--       let ydg := revDerivUpdate K (fun wx : W×X => g wx.1 wx.2) (w,xda0.1)
--       let zdf := revDerivUpdate K (fun wy : W×Y => f wy.1 wy.2) (w,ydg.1)
--       (zdf.1, 
--        fun dz k dw => 
--          let dwy := zdf.2 dz k (dw,0)
--          let dwx := ydg.2 dwy.2 1 (dwy.1,0)
--          let dw  := xda0.2 dwx.2 1 dwx.1
--          dw) := 
-- by 
--   sorry_proof
--   unfold Function.comp; ftrans
--   funext w
--   simp[revDerivUpdate]
--   funext dz k dx
--   have h : IsLinearMap K (semiAdjoint K (cderiv K (fun x0x1 => g x0x1.fst x0x1.snd) (w, a0 w))) := sorry_proof
--   have h' : IsLinearMap K (Prod.snd : W×X→X) := sorry_proof
--   have h'' : IsLinearMap K (semiAdjoint K (cderiv K a0 w)) := sorry_proof
--   rw[h.map_smul]
--   rw[h'.map_smul]
--   rw[h''.map_smul]
--   simp


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revDerivUpdate_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x + g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 + ydg.1, fun dy dx => ydg.2 dy (ydf.2 dy dx)) := 
by 
  unfold revDerivUpdate
  ftrans; funext x; simp[add_assoc]


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.revDerivUpdate_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x - g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let ydg := revDerivUpdate K g x
      (ydf.1 - ydg.1, fun dy dx => ydg.2 (-dy) (ydf.2 dy dx)) := 
by 
  unfold revDerivUpdate
  ftrans; funext x; simp; sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revDerivUpdate_rule
  (f : X → Y)
  : (revDerivUpdate K fun x => - f x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      (-ydf.1, fun dy dx => ydf.2 (-dy) dx) :=
by 
  unfold revDerivUpdate; funext x; ftrans; simp; sorry_proof


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[ftrans]
theorem HMul.hMul.arg_a0a1.revDerivUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x * g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 * zdg.1, fun dy dx => ydf.2 ((conj zdg.1)*dy)  (zdg.2 (conj ydf.1* dy)  dx)) :=
by 
  unfold revDerivUpdate; 
  funext x; ftrans; simp[mul_assoc,mul_comm,add_assoc]; sorry_proof
  


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivUpdate_rule
  {Y : Type _} [SemiHilbert K Y]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 • zdg.1, fun dy dx => ydf.2 (inner zdg.1 dy) (zdg.2 (conj ydf.1•dy) dx)) :=
by 
  unfold revDerivUpdate; 
  funext x; ftrans; simp[mul_assoc,mul_comm,add_assoc]; sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revDerivUpdate_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0)
  : (revDerivUpdate K fun x => f x / g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 / zdg.1, 
       -- fun dy k dx => (1 / (conj zdg.1)^2) • (conj zdg.1 • ydf.2 dy - conj ydf.1 • zdg.2 dy)) :=
       fun dy dx =>  
         let factor := ((conj zdg.1)^2)⁻¹
         let dy := factor * dy
         zdg.2 (-conj ydf.1 * dy) (ydf.2 (conj zdg.1 * dy) dx)) :=

by 
  unfold revDerivUpdate; 
  funext x; ftrans; simp[mul_assoc,mul_comm,add_assoc]; sorry_proof


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.revDerivUpdate_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revDerivUpdate K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      (ydf.1 ^ n, 
       fun dy dx => ydf.2 (n * (conj ydf.1 ^ (n-1)) * dy) dx) :=
by 
  unfold revDerivUpdate; 
  funext x; ftrans; simp[mul_assoc,mul_comm,add_assoc]; funext dy dx; sorry_proof



-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.revDerivUpdate_rule {ι : Type _} [EnumType ι]
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (fun x => f x i))
  : revDerivUpdate K (fun x => ∑ i, f x i)
    =
    fun x => 
      let ydf := fun i => revDerivUpdate K (fun x => f x i) x
      (∑ i, (ydf i).1, 
       fun dy dx => revDerivUpdate.fun_fold (fun i : ι => (ydf i).2 dy) dx) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  simp [revDerivUpdate]
  funext x; simp; sorry_proof



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
theorem Inner.inner.arg_a0a1.revDerivUpdate_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : (revDerivUpdate R fun x => ⟪f x, g x⟫[R])
    =
    fun x => 
      let y₁df := revDerivUpdate R f x
      let y₂dg := revDerivUpdate R g x
      let dx₁ := y₁df.2 y₂dg.1
      let dx₂ := y₂dg.2 y₁df.1
      (⟪y₁df.1, y₂dg.1⟫[R],
       fun dr dx => 
         -- conj dr • dx₁ + dr • dx₂):=
         y₂dg.2 (dr • y₁df.1) (y₁df.2 (conj dr • y₂dg.1) dx) ) := 

by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  simp[revDerivUpdate]
  funext x; simp; sorry_proof


@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.revDerivUpdate_rule
  (f : X → Y)
  (hf : HasAdjDiff R f) 
  : (revDerivUpdate R fun x => ‖f x‖₂²[R])
    =
    fun x => 
      let ydf := revDerivUpdate R f x
      let ynorm2 := ‖ydf.1‖₂²[R]
      (ynorm2,
       fun dr dx => 
          ydf.2 (((2:R)*dr)•ydf.1) dx) :=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revDerivUpdate]
  ftrans only
  simp
  ftrans
  sorry_proof


@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivUpdate_rule_at
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivUpdate R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr dx => 
       ydf.2 ((ynorm⁻¹ * dr)•ydf.1) dx):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivUpdate]
  ftrans only
  simp
  ftrans
  funext dr; sorry_proof

end InnerProductSpace

