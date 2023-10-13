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
  (f : X → Y) (x : X) : Y×(Y→K→X→X) :=
  (f x, fun dy k dx => dx + k • semiAdjoint K (cderiv K f x) dy)

-- @[fprop]
-- theorem asdf (f : X → Y) (x : X) (k : K) (hf : HasAdjDiff K f)
--   : HasSemiAdjoint K (fun y => (revDerivUpdate K f x).2 y k 0) := by unfold revDerivUpdate; ftrans; fprop


namespace revDerivUpdate


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule
  : revDerivUpdate K (fun x : X => x) = fun x => (x, fun dx' k dx => dx + k • dx') :=
by
  unfold revDerivUpdate
  funext _; ftrans; ftrans


theorem const_rule (y : Y)
  : revDerivUpdate K (fun _ : X => y) = fun x => (y, fun _ k dx => dx) :=
by
  unfold revDerivUpdate
  funext _; ftrans; ftrans
variable {X}

variable (E)
theorem proj_rule (i : ι)
  : revDerivUpdate K (fun (x : (i:ι) → E i) => x i)
    = 
    fun x => 
      (x i, fun dxi k dx j => if h : i=j then dx j + k • h ▸ dxi else dx j) :=
by
  unfold revDerivUpdate
  funext _; ftrans; ftrans; funext dxi k dx j; simp; sorry_proof
variable {E}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K f ydg.1
      (zdf.1,
       fun dz k dx =>
         let dy := zdf.2 dz 1 0
         ydg.2 dy k dx)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext _; ftrans; ftrans; simp

theorem comp_rule'
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun x' => f (ydg.1 + semiAdjoint K (ydg.2 · 1 0) x')) 0
      zdf := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext _; simp; ftrans


theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz k dx => 
         let dxdy := zdf.2 dz k (dx, 0)
         let dx := ydg.2 dxdy.2 1 dxdy.1
         dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext x; ftrans; ftrans; simp 
  funext dz k dx
  simp[add_assoc]
  have h : IsLinearMap K (semiAdjoint K (cderiv K g x)) := sorry_proof
  rw[h.map_smul]

theorem let_rule'
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDerivUpdate K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revDerivUpdate K g x
      let zdf := revDerivUpdate K (fun x' => f (x + x') (ydg.1 + semiAdjoint K (ydg.2 · 1 0) x')) 0
      zdf :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate
  funext x; simp; ftrans


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
       fun dy k dx => fun_fold (fun i => (xdf i).2 (dy i) k) dx)
       :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revDerivUpdate
  funext _; ftrans; ftrans; -- simp
  funext dy dx
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
      ((ydg.1,zdf.1), fun dyz k dx => zdf.2 dyz.2 k (ydg.2 dyz.1 k dx)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; simp; ftrans; ftrans; simp[add_assoc]

 
theorem Prod.mk.arg_fstsnd.revDerivUpdate_rule_simple
  : revDerivUpdate K (fun xy : X × Y => (xy.1, xy.2))
    =
    fun xy => 
      (xy, fun (dx',dy') k (dx,dy) => (dx+k•dx', dy+k•dy')) := 
by 
  unfold revDerivUpdate; 
  funext (x,y); simp
  funext (dx',dy') k (dx,dy); ftrans; ftrans; simp


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.revDerivUpdate_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x).1)
    =
    fun x => 
      let yzdf := revDerivUpdate K f x
      (yzdf.1.1, fun dy k dx => yzdf.2 (dy,0) k dx) := 
by 
  have ⟨_,_⟩ := hf
  unfold revDerivUpdate; ftrans; ftrans; simp


theorem Prod.fst.arg_self.revDerivUpdate_rule_simple
  : revDerivUpdate K (fun xy : X×Y => xy.1)
    =
    fun xy => 
      (xy.1, fun dx' k (dx,dy) => (dx+k•dx', dy)) := 
by 
  unfold revDerivUpdate;
  funext (x,y); simp; ftrans;
  funext dx' k (dx,dy); ftrans; ftrans; simp


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.revDerivUpdate_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revDerivUpdate K (fun x => (f x).2)
    =
    fun x => 
      let yzdf := revDerivUpdate K f x
      (yzdf.1.2, fun dz k dx => yzdf.2 (0,dz) k dx) := 
by 
  have ⟨_,_⟩ := hf
  unfold revDerivUpdate; ftrans; ftrans; simp

theorem Prod.snd.arg_self.revDerivUpdate_simple_rule
  : revDerivUpdate K (fun xy : X×Y => xy.2)
    =
    fun xy => 
      (xy.2, fun dy' k (dx,dy) => (dx, dy + k•dy')) := 
by 
  unfold revDerivUpdate;
  funext (x,y); simp; ftrans;
  funext dy' k (dx,dy); ftrans; ftrans; simp


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
      (ydf.1 + ydg.1, fun dy k dx => ydg.2 dy k (ydf.2 dy k dx)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; simp; ftrans; ftrans; simp[add_assoc]


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
      (ydf.1 - ydg.1, fun dy k dx => ydf.2 dy k (ydg.2 dy (-k) dx)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; simp; ftrans; ftrans; funext x; simp; funext dy k dx; 
  simp[add_assoc]
  rw[sub_eq_add_neg]
  rw[smul_add]
  rw[smul_neg]
  rw[add_comm]


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revDerivUpdate_rule
  (f : X → Y)
  : (revDerivUpdate K fun x => - f x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      (-ydf.1, fun dy k dx => ydf.2 dy (-k) dx) :=
by 
  unfold revDerivUpdate; simp; ftrans; ftrans


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
      (ydf.1 * zdg.1, fun dy k dx => ydf.2 dy (k * conj zdg.1) (zdg.2 dy (k * conj ydf.1) dx)) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; simp; ftrans; ftrans;
  funext x;
  simp
  funext dy k dx
  simp[smul_smul, add_assoc]
  


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revDerivUpdate_rule
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revDerivUpdate K fun x => f x • g x)
    =
    fun x => 
      let ydf := revDerivUpdate K f x
      let zdg := revDerivUpdate K g x
      (ydf.1 • zdg.1, fun dy k dx => ydf.2 (inner zdg.1 dy) k (zdg.2 dy (k*conj ydf.1) dx)) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; simp; ftrans; ftrans;
  funext x; simp; funext dy k dx
  simp[add_assoc,smul_smul]

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
       fun dy k dx =>  
         let factor := ((conj zdg.1)^2)⁻¹
         zdg.2 dy (k * factor * (-conj ydf.1)) (ydf.2 dy (k * factor * conj zdg.1) dx)) :=

by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revDerivUpdate; simp; ftrans; ftrans; simp
  funext x; simp; funext dy k dx
  simp[add_assoc,smul_smul,smul_sub,sub_eq_add_neg,mul_assoc]


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
       fun dy k dx => ydf.2 dy (k * n * (conj ydf.1 ^ (n-1))) dx) :=
by 
  have ⟨_,_⟩ := hf
  funext x
  unfold revDerivUpdate; simp; funext dy k dx; ftrans; ftrans; simp[smul_smul]; ring_nf



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
       fun dy k dx => revDerivUpdate.fun_fold (fun i : ι => (ydf i).2 dy k) dx) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  simp [revDerivUpdate]
  funext x; simp; funext dy k dx
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
       fun dr k dx => 
         -- conj dr • dx₁ + dr • dx₂):=
         y₂dg.2 y₁df.1 (k * dr) (y₁df.2 y₂dg.1 (k * conj dr) dx) ) := 

by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  simp[revDerivUpdate]
  funext x; simp; funext dr k dx
  ftrans
  simp
  ftrans
  simp [smul_smul,add_assoc]


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
       fun dr k dx => 
          ydf.2 ydf.1 (k * 2 * dr) dx) :=
by 
  have ⟨_,_⟩ := hf
  funext x; simp[revDerivUpdate]
  ftrans only
  simp
  ftrans
  simp[smul_smul,mul_assoc]


@[ftrans]
theorem SciLean.norm₂.arg_x.revDerivUpdate_rule_at
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : (revDerivUpdate R (fun x => ‖f x‖₂[R]) x)
    =
    let ydf := revDerivUpdate R f x
    let ynorm := ‖ydf.1‖₂[R]
    (ynorm,
     fun dr k dx => 
       ydf.2 ydf.1 (k * ynorm⁻¹ * dr) dx):=
by 
  have ⟨_,_⟩ := hf
  simp[revDerivUpdate]
  ftrans only
  simp
  ftrans
  funext dr; simp[smul_smul,mul_assoc]

end InnerProductSpace

