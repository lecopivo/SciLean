import SciLean.Core.FunctionTransformations.CDeriv

namespace SciLean

noncomputable
def fwdCDeriv
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  (f : X → Y) (x dx : X) : Y×Y :=
  (f x, cderiv K f x dx)


namespace fwdCDeriv

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


theorem fwdCDeriv_of_linear (f : X → Y) (hf : IsSmoothLinearMap K f)
  : fwdCDeriv K f = fun x dx => (f x, f dx) := by unfold fwdCDeriv; simp [cderiv_of_linear _ hf]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (K)

variable (X)
theorem id_rule 
  : fwdCDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdCDeriv; ftrans

theorem const_rule (y : Y)
  : fwdCDeriv K (fun _ : X => y) = fun x dx => (y, 0) :=
by
  unfold fwdCDeriv; ftrans
variable {X}

variable (E)
theorem proj_rule (i : ι)
  : fwdCDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) :=
by
  unfold fwdCDeriv; ftrans
variable {E}


theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : fwdCDeriv K (fun x : X => f (g x)) 
    = 
    fun x dx => 
      let ydy := fwdCDeriv K g x dx 
      let zdz := fwdCDeriv K f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdCDeriv; ftrans


theorem let_rule 
  (f : X → Y → Z) (g : X → Y)
  (hf : IsDifferentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : IsDifferentiable K g)
  : fwdCDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x dx => 
      let ydy := fwdCDeriv K g x dx 
      let zdz := fwdCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdCDeriv; ftrans


theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsDifferentiable K (f · i))
  : (fwdCDeriv K fun (x : X) (i : ι) => f x i)
    = 
    fun x dx =>
      (fun i => f x i, fun i => (fwdCDeriv K (f · i) x dx).2) := 
by 
  unfold fwdCDeriv; ftrans


theorem comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : IsDifferentiableAt K f (g x)) (hg : IsDifferentiableAt K g x)
  : fwdCDeriv K (fun x : X => f (g x)) x
    = 
    fun dx => 
      let ydy := fwdCDeriv K g x dx 
      let zdz := fwdCDeriv K f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdCDeriv; ftrans


theorem let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)  
  (hf : IsDifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x)) (hg : IsDifferentiableAt K g x)
  : fwdCDeriv K (fun x : X => let y := g x; f x y) x
    = 
    fun dx => 
      let ydy := fwdCDeriv K g x dx 
      let zdz := fwdCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdCDeriv; ftrans


theorem pi_rule_at  
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, IsDifferentiableAt K (f · i) x)
  : (fwdCDeriv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      (fun i => f x i, fun i => (fwdCDeriv K (f · i) x dx).2) := 
by 
  unfold fwdCDeriv; ftrans



-- Register `fwdCDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq

def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `fwdCDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``fwdCDeriv

  getFTransFun? e := 
    if e.isAppOf ``fwdCDeriv then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``fwdCDeriv then
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


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdCDeriv, ftransExt))


end SciLean.fwdCDeriv

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {W : Type _} [Vec K W]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.fwdCDeriv_rule_at
  (x : X)
  (g : X → Y) (hg : IsDifferentiableAt K g x)
  (f : X → Z) (hf : IsDifferentiableAt K f x)
  : fwdCDeriv K (fun x => (g x, f x)) x
    =
    fun dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := 
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem Prod.mk.arg_fstsnd.fwdCDeriv_rule
  (g : X → Y) (hg : IsDifferentiable K g)
  (f : X → Z) (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun x => (g x, f x))
    =    
    fun x dx =>
      let ydy := fwdCDeriv K g x dx
      let zdz := fwdCDeriv K f x dx
      ((ydy.1, zdz.1), (ydy.2, zdz.2)) := 
by 
  unfold fwdCDeriv; ftrans

 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.fwdCDeriv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : IsDifferentiableAt K f x)
  : fwdCDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := 
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem Prod.fst.arg_self.fwdCDeriv_rule
  (f : X → Y×Z) (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun x => (f x).1)
    =
    fun x dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) :=
by 
  unfold fwdCDeriv; ftrans



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.fwdCDeriv_rule_at
  (x : X)
  (f : X → Y×Z) (hf : IsDifferentiableAt K f x)
  : fwdCDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem Prod.snd.arg_self.fwdCDeriv_rule
  (f : X → Y×Z) (hf : IsDifferentiable K f)
  : fwdCDeriv K (fun x => (f x).2)
    =
    fun x dx =>
      let yzdyz := fwdCDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold fwdCDeriv; ftrans


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Function.comp.arg_fga0.fwdCDeriv_rule 
  (f : W → Y → Z) (g : W → X → Y) (a0 : W → X)
  (hf : IsDifferentiable K (fun wy : W×Y => f wy.1 wy.2))
  (hg : IsDifferentiable K (fun wx : W×X => g wx.1 wx.2))
  (ha0 : IsDifferentiable K a0)
  : fwdCDeriv K (fun w => ((f w) ∘ (g w)) (a0 w))
    =
    fun w dw => 
      let xdx := fwdCDeriv K a0 w dw
      let ydy := fwdCDeriv K (fun wx : W×X => g wx.1 wx.2) (w,xdx.1) (dw,xdx.2)
      let zdz := fwdCDeriv K (fun wy : W×Y => f wy.1 wy.2) (w,ydy.1) (dw,ydy.2)
      zdz := 
by 
  unfold Function.comp; ftrans

-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fwdCDeriv_rule_at
  (x : X) (f g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (fwdCDeriv K fun x => f x + g x) x
    =
    fun dx =>
      fwdCDeriv K f x dx + fwdCDeriv K g x dx := 
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.fwdCDeriv_rule
  (f g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (fwdCDeriv K fun x => f x + g x)
    =
    fun x dx =>
      fwdCDeriv K f x dx + fwdCDeriv K g x dx := 
by 
  unfold fwdCDeriv; ftrans



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.fwdCDeriv_rule_at
  (x : X) (f g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (fwdCDeriv K fun x => f x - g x) x
    =
    fun dx =>
      fwdCDeriv K f x dx - fwdCDeriv K g x dx := 
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem HSub.hSub.arg_a0a1.fwdCDeriv_rule
  (f g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (fwdCDeriv K fun x => f x - g x)
    =
    fun x dx =>
      fwdCDeriv K f x dx - fwdCDeriv K g x dx :=
by 
  unfold fwdCDeriv; ftrans



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.fwdCDeriv_rule_at
  (x : X) (f : X → Y)
  : (fwdCDeriv K fun x => - f x) x
    =
    fun dx => - fwdCDeriv K f x dx :=
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem Neg.neg.arg_a0.fwdCDeriv_rule
  (f : X → Y)
  : (fwdCDeriv K fun x => - f x)
    =
    fun x dx => - fwdCDeriv K f x dx :=
by  
  unfold fwdCDeriv; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HMul.hMul.arg_a0a1.fwdCDeriv_rule_at
  (x : X) (f g : X → K)
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (fwdCDeriv K fun x => f x * g x) x
    =
    fun dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) :=
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem HMul.hMul.arg_a0a1.fwdCDeriv_rule
  (f g : X → K)
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (fwdCDeriv K fun x => f x * g x)
    =
    fun x dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 * zdz.1, zdz.2 * ydy.1 + ydy.2 * zdz.1) :=
by 
  unfold fwdCDeriv; ftrans


-- HSMul.hSMul -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fwdCDeriv_rule_at
  (x : X) (f : X → K) (g : X → Y) 
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : (fwdCDeriv K fun x => f x • g x) x
    =
    fun dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) :=
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem HSMul.hSMul.arg_a0a1.fwdCDeriv_rule
  (f : X → K) (g : X → Y) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : (fwdCDeriv K fun x => f x • g x)
    =
    fun x dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 • zdz.1, ydy.1 • zdz.2 + ydy.2 • zdz.1) :=
by 
  unfold fwdCDeriv; ftrans


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fwdCDeriv_rule_at
  (x : X) (f : X → K) (g : X → K) 
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x) (hx : g x ≠ 0)
  : (fwdCDeriv K fun x => f x / g x) x
    =
    fun dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) :=
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.fwdCDeriv_rule
  (f : X → K) (g : X → K) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g) (hx : ∀ x, g x ≠ 0)
  : (fwdCDeriv K fun x => f x / g x)
    =
    fun x dx =>
      let ydy := (fwdCDeriv K f x dx)
      let zdz := (fwdCDeriv K g x dx)
      (ydy.1 / zdz.1, (ydy.2 * zdz.1 - ydy.1 * zdz.2) / zdz.1^2) :=
by 
  unfold fwdCDeriv; ftrans


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.fwdCDeriv_rule_at
  (n : Nat) (x : X) (f : X → K) (hf : IsDifferentiableAt K f x) 
  : fwdCDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := fwdCDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
def HPow.hPow.arg_a0.fwdCDeriv_rule
  (n : Nat) (f : X → K) (hf : IsDifferentiable K f) 
  : fwdCDeriv K (fun x => f x ^ n)
    =
    fun x dx =>
      let ydy := fwdCDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold fwdCDeriv; ftrans


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.fwdCDeriv_rule_at
  (f : X → ι → Y) (x : X) (hf : ∀ i, IsDifferentiableAt K (f · i) x)
  : fwdCDeriv K (fun x => ∑ i, f x i) x
    =
    fun dx => 
      let ydy := fwdCDeriv K (fun i => f · i) x dx
      (∑ i, ydy.1 i, ∑ i, ydy.2 i) :=
by
  unfold fwdCDeriv; ftrans

@[ftrans]
theorem SciLean.EnumType.sum.arg_f.fwdCDeriv_rule
  (f : X → ι → Y) (hf : ∀ i, IsDifferentiable K (f · i))
  : fwdCDeriv K (fun x => ∑ i, f x i)
    =
    fun x dx => 
      let ydy := fwdCDeriv K (fun i => f · i) x dx
      (∑ i, ydy.1 i, ∑ i, ydy.2 i) :=
by
  unfold fwdCDeriv; ftrans


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
theorem ite.arg_te.fwdCDeriv_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  : fwdCDeriv K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (fwdCDeriv K t y) (fwdCDeriv K e y) := 
by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]

@[ftrans]
theorem dite.arg_te.fwdCDeriv_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (e : ¬c → X → Y)
  : fwdCDeriv K (fun x => dite c (t · x) (e · x))
    =
    fun y =>
      dite c (fun p => fwdCDeriv K (t p) y) 
             (fun p => fwdCDeriv K (e p) y) := 
by
  induction dec
  case isTrue h  => ext y; simp[h]; simp[h]
  case isFalse h => ext y; simp[h]; simp[h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable
  {R : Type _} [RealScalar R]
  {X : Type _} [Vec R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[ftrans]
theorem Inner.inner.arg_a0a1.fwdCDeriv_rule
  (f : X → Y) (g : X → Y)
  (hf : IsDifferentiable R f) (hg : IsDifferentiable R g)
  : fwdCDeriv R (fun x => ⟪f x, g x⟫[R])
    =
    fun x dx =>
      let y₁dy₁ := fwdCDeriv R f x dx
      let y₂dy₂ := fwdCDeriv R g x dx
      (⟪y₁dy₁.1, y₂dy₂.1⟫[R], 
       ⟪y₁dy₁.2, y₂dy₂.1⟫[R] + ⟪y₁dy₁.1, y₂dy₂.2⟫[R]) := 
by 
  unfold fwdCDeriv; ftrans


@[ftrans]
theorem SciLean.Norm2.norm2.arg_a0.fwdCDeriv_rule
  (f : X → Y) 
  (hf : IsDifferentiable R f)
  : fwdCDeriv R (fun x => ‖f x‖₂²[R])
    =
    fun x dx => 
      let ydy := fwdCDeriv R f x dx
      (‖ydy.1‖₂²[R], 2 * ⟪ydy.2, ydy.1⟫[R]) := 
by
  unfold fwdCDeriv
  funext x dx
  ftrans; simp

open Scalar in
@[ftrans]
theorem SciLean.norm₂.arg_x.fwdCDeriv_rule
  (f : X → Y) (x : X)
  (hf : IsDifferentiableAt R f x) (hx : f x≠0)
  : fwdCDeriv R (fun x => ‖f x‖₂[R]) x
    =
    fun dx => 
      let ydy := fwdCDeriv R f x dx
      let ynorm := ‖ydy.1‖₂[R]
      (ynorm, ynorm⁻¹ * ⟪ydy.2,ydy.1⟫[R]) :=
by
  unfold fwdCDeriv
  funext dx
  ftrans; simp

end InnerProductSpace
