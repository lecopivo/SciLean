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

theorem id_rule 
  : fwdDeriv K (fun x : X => x) = fun x dx => (x,dx) :=
by
  unfold fwdDeriv
  simp


theorem const_rule (x :X)
  : fwdDeriv K (fun _ : Y => x) = fun y dy => (x, 0) :=
by
  unfold fwdDeriv
  funext y dy
  simp


theorem comp_rule 
  (g : X → Y) (hg : Differentiable K g)
  (f : Y → Z) (hf : Differentiable K f)
  : fwdDeriv K (fun x : X => f (g x)) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdDeriv
  funext x dx; congr
  rw[fderiv.comp_rule g hg f hf]
  simp


theorem let_rule 
  (g : X → Y) (hg : Differentiable K g)
  (f : X → Y → Z) (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2))
  : fwdDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdDeriv
  funext x dx;
  rw[fderiv.let_rule g hg f hf]
  simp


theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (fwdDeriv K fun (x : X) (i : ι) => f i x)
    = 
    fun x dx =>
      (fun i => f i x, fun i => (fwdDeriv K (f i) x dx).2) := 
by 
  unfold fwdDeriv
  funext x; rw[fderiv_pi (fun i => hf i x)]
  simp


theorem comp_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : Y → Z) (hf : DifferentiableAt K f (g x))
  : fwdDeriv K (fun x : X => f (g x)) x
    = 
    fun dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K f ydy.1 ydy.2 
      zdz :=
by
  unfold fwdDeriv
  funext dx; congr
  rw[fderiv.comp_rule_at x g hg f hf]
  simp


theorem let_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : X → Y → Z) (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x))
  : fwdDeriv K (fun x : X => let y := g x; f x y) x
    = 
    fun dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz :=
by
  unfold fwdDeriv
  funext dx;
  rw[fderiv.let_rule_at x g hg f hf]
  simp


theorem pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (fwdDeriv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx =>
      (fun i => f i x, fun i => (fwdDeriv K (f i) x dx).2) := 
by 
  unfold fwdDeriv
  rw[fderiv.pi_rule_at x f hf]
  simp



-- Register `fwdDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------
#check `(tactic| assumption) 
#check Lean.Syntax

open Lean Meta Qq

def fwdDeriv.discharger (e : Expr) : SimpM (Option Expr) := do
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
def fwdDeriv.ftransExt : FTransExt where
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

  idRule    := tryNamedTheorem ``fderiv.id_rule fderiv.discharger
  constRule := tryNamedTheorem ``fderiv.const_rule fderiv.discharger
  projRule  := tryNamedTheorem ``fderiv.proj_rule fderiv.discharger
  compRule  e f g := do

    let (args, bis, type) ← 
      forallMetaTelescope (← inferType (← mkConstWithLevelParams ``fderiv.comp_rule))

    let gf := args[11]!
    let Hg := args[12]!
    let mf := args[13]!
    let Hf := args[14]!

    mf.mvarId!.assign f
    gf.mvarId!.assign g

    let lhs := type.appFn!.appArg!
    let rhs := type.appArg!

    if ¬(← isDefEq e lhs) then
      trace[Meta.Tactic.ftrans.unify] "{``fderiv.comp_rule}, failed to unify\n{lhs}\nwith\n{e}"
      return none
    else
      
      let .some hf ← fderiv.discharger Hf
        | trace[Meta.Tactic.fprop.discharge] "{``fderiv.comp_rule},, failed to discharge hypotheses {Hf}"
          return none

      let .some hg ← fderiv.discharger Hg
        | trace[Meta.Tactic.fprop.discharge] "{``fderiv.comp_rule},, failed to discharge hypotheses {Hg}"
          return none

      let proof ← mkAppM ``fderiv.comp_rule #[g, hg, f, hf]
      
      return .some (.visit { expr := (← instantiateMVars rhs), proof? := proof})

  letRule e f g := do

    let (args, bis, type) ← 
      forallMetaTelescope (← inferType (← mkConstWithLevelParams ``fderiv.let_rule))

    let gf := args[11]!
    let Hg := args[12]!
    let mf := args[13]!
    let Hf := args[14]!

    mf.mvarId!.assign f
    gf.mvarId!.assign g

    let lhs := type.appFn!.appArg!
    let rhs := type.appArg!

    if ¬(← isDefEq e lhs) then
      trace[Meta.Tactic.ftrans.unify] "{``fderiv.let_rule}, failed to unify\n{lhs}\nwith\n{e}"
      return none
    else
      
      let .some hf ← fderiv.discharger Hf
        | trace[Meta.Tactic.fprop.discharge] "{``fderiv.let_rule},, failed to discharge hypotheses {Hf}"
          return none

      let .some hg ← fderiv.discharger Hg
        | trace[Meta.Tactic.fprop.discharge] "{``fderiv.let_rule},, failed to discharge hypotheses {Hg}"
          return none

      let proof ← mkAppM ``fderiv.let_rule #[g, hg, f, hf]
      
      return .some (.visit { expr := (← instantiateMVars rhs), proof? := proof})

  piRule  e f := tryNamedTheorem ``fderiv.pi_rule fderiv.discharger e

  discharger := fderiv.discharger
  -- identityRule     := .some <| .thm ``id_rule
  -- constantRule     := .some <| .thm ``const_rule
  -- compRule         := .some <| .thm ``comp_rule
  -- lambdaLetRule    := .some <| .thm ``let_rule
  -- lambdaLambdaRule := .some <| .thm ``pi_rule



-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``fwdDeriv, fwdDeriv.ftransExt))


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

@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.fwdDeriv_at_comp
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


@[ftrans_rule]
theorem Prod.mk.arg_fstsnd.fwdDeriv_comp
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

@[ftrans_rule]
theorem Prod.fst.arg_self.fwdDeriv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fwdDeriv K (fun x => (f x).1) x
    =
    fun dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.1, yzdyz.2.1) := 
by 
  unfold fwdDeriv; ftrans


@[ftrans_rule]
theorem Prod.fst.arg_self.fwdDeriv_comp
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

@[ftrans_rule]
theorem Prod.snd.arg_self.fwdDeriv_at_comp
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt K f x)
  : fwdDeriv K (fun x => (f x).2) x
    =
    fun dx =>
      let yzdyz := fwdDeriv K f x dx
      (yzdyz.1.2, yzdyz.2.2) := 
by 
  unfold fwdDeriv; ftrans


@[ftrans_rule]
theorem Prod.snd.arg_self.fwdDeriv_comp
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

@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.fwdDeriv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fwdDeriv K fun x => f x + g x) x
    =
    fun dx =>
      fwdDeriv K f x dx + fwdDeriv K g x dx := 
by 
  unfold fwdDeriv; ftrans


@[ftrans_rule]
theorem HAdd.hAdd.arg_a4a5.fwdDeriv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K fun x => f x + g x)
    =
    fun x dx =>
      fwdDeriv K f x dx + fwdDeriv K g x dx := 
by 
  unfold fwdDeriv; ftrans



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HSub.hSub.arg_a4a5.fwdDeriv_at_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt K f x) (hg : DifferentiableAt K g x)
  : (fwdDeriv K fun x => f x - g x) x
    =
    fun dx =>
      fwdDeriv K f x dx - fwdDeriv K g x dx := 
by 
  unfold fwdDeriv; ftrans


@[ftrans_rule]
theorem HSub.hSub.arg_a4a5.fwdDeriv_comp
  (f g : X → Y) (hf : Differentiable K f) (hg : Differentiable K g)
  : (fwdDeriv K fun x => f x - g x)
    =
    fun x dx =>
      fwdDeriv K f x dx - fwdDeriv K g x dx :=
by 
  unfold fwdDeriv; ftrans



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem Neg.neg.arg_a2.fwdDeriv_at_comp
  (x : X) (f : X → Y)
  : (fwdDeriv K fun x => - f x) x
    =
    fun dx => - fwdDeriv K f x dx :=
by 
  unfold fwdDeriv; ftrans


@[ftrans_rule]
theorem Neg.neg.arg_a2.fwdDeriv_comp
  (f : X → Y)
  : (fwdDeriv K fun x => - f x)
    =
    fun x dx => - fwdDeriv K f x dx :=
by  
  unfold fwdDeriv; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem HMul.hMul.arg_a4a5.fwdDeriv_at_comp
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


@[ftrans_rule]
theorem HMul.hMul.arg_a4a5.fwdDeriv_comp
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


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans_rule]
theorem SMul.smul.arg_a3a4.fwdDeriv_at_comp
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


@[ftrans_rule]
theorem SMul.smul.arg_a3a4.fwdDeriv_comp
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

@[ftrans_rule]
theorem HDiv.hDiv.arg_a4a5.fwdDeriv_at_comp
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


@[ftrans_rule]
theorem HDiv.hDiv.arg_a4a5.fwdDeriv_comp
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


-- HPow.hPow ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans_rule]
def HPow.hPow.arg_a4.fwdDeriv_at_comp
  (n : Nat) (x : X) (f : X → K) (hf : DifferentiableAt K f x) 
  : fwdDeriv K (fun x => f x ^ n) x
    =
    fun dx =>
      let ydy := fwdDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold fwdDeriv; ftrans


@[ftrans_rule]
def HPow.hPow.arg_a4.fwdDeriv_comp
  (n : Nat) (f : X → K) (hf : Differentiable K f) 
  : fwdDeriv K (fun x => f x ^ n)
    =
    fun x dx =>
      let ydy := fwdDeriv K f x dx
      (ydy.1 ^ n, n * ydy.2 * (ydy.1 ^ (n-1))) :=
by 
  unfold fwdDeriv; ftrans
