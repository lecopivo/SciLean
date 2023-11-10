import SciLean.Core.FunctionTransformations.FDeriv
import SciLean.Core.FunctionTransformations.Adjoint

set_option linter.unusedVariables false

namespace SciLean

open ContinuousLinearMap

noncomputable
def revFDeriv
  (K : Type _) [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, ContinuousLinearMap.adjoint (fderiv K f x))


namespace revFDeriv

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule 
  : revFDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) :=
by
  unfold revFDeriv
  funext _
  ftrans; ftrans; ext; simp; simp
  


theorem const_rule (y : Y)
  : revFDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) :=
by
  unfold revFDeriv
  funext _
  ftrans; ftrans; ext; simp; simp
variable{X}

variable(E)
theorem proj_rule [DecidableEq ι] (i : ι)
  : revFDeriv K (fun (x : PiLp 2 (fun (_ : ι) => X)) => x i)
    = 
    fun x => 
      (x i, fun dxi j => if i=j then dxi else (0 : X)) :=
by
  unfold revFDeriv
  funext _; ext; dsimp; dsimp
  -- Here we are in trouble because fderiv depends on the norm
  have h : (fderiv K fun (x : PiLp 2 (fun (_ : ι) => X)) => x i)
           =
           fun _ => fun dx =>L[K] dx i := sorry_proof -- by apply fderiv.proj_rule 
  rw[h]
  dsimp; ftrans only; sorry_proof -- do not understand why simp does not solve this
variable {E}

theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : revFDeriv K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revFDeriv K g x
      let zdf := revFDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := 
by
  unfold revFDeriv
  funext _
  ftrans; -- ftrans; simp
  -- ext; simp
  sorry_proof

theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g)
  : revFDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revFDeriv K g x 
      let zdf := revFDeriv K (fun (xy : X×₂Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  :=
by sorry_proof  -- here we are running to the problem that fderiv on `X×Y` is different from fderiv on `ProdLp p E`


open BigOperators in
theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (revFDeriv K (Y:= PiLp 2 E) fun (x : X) (i : ι) => f i x)
    =
    fun x =>
      let xdf := fun i =>
        (revFDeriv K fun (x : X) => f i x) x
      (fun i => (xdf i).1,
       fun dy => ∑ i, (xdf i).2 (dy i))
       :=
by sorry_proof  -- here we are running to the problem that fderiv on `(i:ι) → E i` is different from fderiv on `PiLp p E`

theorem comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x)
  : revFDeriv K (fun x : X => f (g x)) x
    = 
    let ydg := revFDeriv K g x
    let zdf := revFDeriv K f ydg.1
    (zdf.1,
     fun dz =>
       let dy := zdf.2 dz
       ydg.2 dy)  := 
by
  unfold revFDeriv
  ftrans; -- ftrans; simp; ext; simp
  sorry_proof

theorem let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x,g x)) (hg : DifferentiableAt K g x)
  : revFDeriv K (fun x : X => let y := g x; f x y) x
    = 
    let ydg := revFDeriv K g x 
    let zdf := revFDeriv K (fun (xy : X×₂Y) => f xy.1 xy.2) (x,ydg.1)
    (zdf.1,
     fun dz => 
       let dxdy := zdf.2 dz
       let dx := ydg.2 dxdy.2
       dxdy.1 + dx)  :=
by sorry_proof  -- here we are running to the problem that fderiv on `X×Y` is different from fderiv on `ProdLp p E`


open BigOperators in
theorem pi_rule_at
  (f : (i : ι) → X → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (revFDeriv K (Y:= PiLp 2 E) fun (x : X) (i : ι) => f i x) x
    =
    let xdf := fun i =>
      (revFDeriv K fun (x : X) => f i x) x
    (fun i => (xdf i).1,
     fun dy => ∑ i, (xdf i).2 (dy i)) :=
by sorry_proof  -- here we are running to the problem that fderiv on `(i:ι) → E i` is different from fderiv on `PiLp p E`


-- Register `revFDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revFDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
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
  ftransName := ``revFDeriv

  getFTransFun? e := 
    if e.isAppOf ``revFDeriv then

      if let .some f := e.getArg? 10 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revFDeriv then
      e.setArg 10 f
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
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revFDeriv, ftransExt))


end SciLean.revFDeriv

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem SciLean.ProdL2.mk.arg_fstsnd.revFDeriv_rule_at
  (g : X → Y) (f : X → Z) (x : X)
  (hg : DifferentiableAt K g x) (hf : DifferentiableAt K f x)
  : revFDeriv K (fun x => ProdL2.mk (g x) (f x)) x
    =
    let ydg := revFDeriv K g x
    let zdf := revFDeriv K f x
    ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := 
by sorry_proof

@[ftrans]
theorem SciLean.ProdL2.mk.arg_fstsnd.revFDeriv_rule
  (g : X → Y) (f : X → Z)
  (hg : Differentiable K g) (hf : Differentiable K f)
  : revFDeriv K (fun x => ProdL2.mk (g x) (f x))
    =
    fun x => 
      let ydg := revFDeriv K g x
      let zdf := revFDeriv K f x
      ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := 
by 
  funext x
  apply SciLean.ProdL2.mk.arg_fstsnd.revFDeriv_rule_at g f x (hg x) (hf x)
 

-- ProdL2.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem SciLean.ProdL2.fst.arg_self.revFDeriv_rule_at
  (f : X → Y×₂Z) (x : X) (hf : DifferentiableAt K f x)
  : revFDeriv K (fun x => ProdL2.fst (f x)) x
    =
    let yzdf := revFDeriv K f x
    (ProdL2.fst yzdf.1, fun dy => yzdf.2 (dy,0)) := 
by sorry_proof

@[ftrans]
theorem SciLean.ProdL2.fst.arg_self.revFDeriv_rule
  (f : X → Y×₂Z) (hf : Differentiable K f)
  : revFDeriv K (fun x => ProdL2.fst (f x))
    =
    fun x => 
      let yzdf := revFDeriv K f x
      (ProdL2.fst yzdf.1, fun dy => yzdf.2 (dy,0)) := 
by sorry_proof


-- ProdL2.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem SciLean.ProdL2.snd.arg_self.revFDeriv_rule_at
  (f : X → Y×₂Z) (x : X) (hf : DifferentiableAt K f x)
  : revFDeriv K (fun x => ProdL2.snd (f x)) x
    =
    let yzdf := revFDeriv K f x
    (ProdL2.snd yzdf.1, fun dz => yzdf.2 (0,dz)) := 
by sorry_proof

@[ftrans]
theorem SciLean.ProdL2.snd.arg_self.revFDeriv_rule
  (f : X → Y×₂Z) (hf : Differentiable K f)
  : revFDeriv K (fun x => ProdL2.snd (f x))
    =
    fun x => 
      let yzdf := revFDeriv K f x
      (ProdL2.snd yzdf.1, fun dz => yzdf.2 (0,dz)) := 
by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revFDeriv_rule_at
  (f g : X → Y) (x : X) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revFDeriv K fun x => f x + g x) x
    =
    let ydf := revFDeriv K f x
    let ydg := revFDeriv K g x
    (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := 
by sorry_proof

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revFDeriv_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (revFDeriv K fun x => f x + g x)
    =
    fun x => 
      let ydf := revFDeriv K f x
      let ydg := revFDeriv K g x
      (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := 
by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.revFDeriv_rule_at
  (f g : X → Y) (x : X) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revFDeriv K fun x => f x - g x) x
    =
    let ydf := revFDeriv K f x
    let ydg := revFDeriv K g x
    (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := 
by sorry_proof

@[ftrans]
theorem HSub.hSub.arg_a0a1.revFDeriv_rule
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (revFDeriv K fun x => f x - g x)
    =
    fun x => 
      let ydf := revFDeriv K f x
      let ydg := revFDeriv K g x
      (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := 
by sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revFDeriv_rule
  (f : X → Y) (x : X) 
  : (revFDeriv K fun x => - f x) x
    =
    let ydf := revFDeriv K f x
    (-ydf.1, fun dy => - ydf.2 dy) :=
by sorry_proof


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HMul.hMul.arg_a0a1.revFDeriv_rule_at
  (f g : X → K) (x : X)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revFDeriv K fun x => f x * g x) x
    =
    let ydf := revFDeriv K f x
    let zdg := revFDeriv K g x
    (ydf.1 / zdg.1, fun dx' =>  zdg.1 • ydf.2 dx' + ydf.1 • zdg.2 dx') :=
by sorry_proof

@[ftrans]
theorem HMul.hMul.arg_a0a1.revFDeriv_rule
  (f g : X → K)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (revFDeriv K fun x => f x * g x)
    =
    fun x => 
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 / zdg.1, fun dx' =>  zdg.1 • ydf.2 dx' + ydf.1 • zdg.2 dx') :=
by sorry_proof


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revFDeriv_rule_at
  (f : X → K) (g : X → Y) (x : X) 
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (revFDeriv K fun x => f x • g x) x
    =
    let ydf := revFDeriv K f x
    let zdg := revFDeriv K g x
    (ydf.1 • zdg.1, fun dx' => ydf.2 (inner dx' zdg.1) + ydf.1 • zdg.2 dx') :=
by sorry_proof

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revFDeriv_rule
  (f : X → K) (g : X → Y)
  (hf : Differentiable K f) (hg : Differentiable K g)
  : (revFDeriv K fun x => f x • g x)
    =
    fun x => 
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 • zdg.1, fun dx' => ydf.2 (inner dx' zdg.1) + ydf.1 • zdg.2 dx') :=
by sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revFDeriv_rule_at
  (f g : X → K) (x : X)
  (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x) (hx : g x ≠ 0)
  : (revFDeriv K fun x => f x / g x) x
    =
    let ydf := revFDeriv K f x
    let zdg := revFDeriv K g x
    (ydf.1 / zdg.1, 
     fun dx' => (1 / zdg.1^2) • (zdg.1 • ydf.2 dx' - ydf.1 • zdg.2 dx')) :=
by sorry_proof

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revFDeriv_rule
  (f g : X → K)
  (hf : Differentiable K f) (hg : Differentiable K g) (hx : ∀ x, g x ≠ 0)
  : (revFDeriv K fun x => f x / g x)
    =
    fun x => 
      let ydf := revFDeriv K f x
      let zdg := revFDeriv K g x
      (ydf.1 / zdg.1, 
       fun dx' => (1 / zdg.1^2) • (zdg.1 • ydf.2 dx' - ydf.1 • zdg.2 dx')) :=
by sorry_proof


-- HPow.hPow ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.revFDeriv_rule_at
  (f : X → K) (x : X) (n : Nat) (hf : DifferentiableAt K f x) 
  : revFDeriv K (fun x => f x ^ n) x
    =
    let ydf := revFDeriv K f x
    (ydf.1 ^ n, fun dx' => (n * (ydf.1 ^ (n-1))) • ydf.2 dx') :=
by sorry_proof

@[ftrans]
def HPow.hPow.arg_a0.revFDeriv_rule
  (f : X → K) (n : Nat) (hf : Differentiable K f) 
  : revFDeriv K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revFDeriv K f x
      (ydf.1 ^ n, fun dx' => (n * (ydf.1 ^ (n-1))) • ydf.2 dx') :=
by sorry_proof
