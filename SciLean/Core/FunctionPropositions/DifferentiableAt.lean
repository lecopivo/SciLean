import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.Core.FunctionPropositions.ContinuousLinearMap

namespace SciLean

namespace DifferentiableAt

variable 
  {R : Type _} [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)]
  

theorem id_rule (x : X)
  : DifferentiableAt R (fun x : X => x) x
  := by simp
  

theorem const_rule (x : X) (y : Y)
  : DifferentiableAt R (fun _ : Y => x) y
  := by simp


theorem comp_rule
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : Y → Z) (hf : DifferentiableAt R f (g x))
  : DifferentiableAt R (fun x => f (g x)) x
  := DifferentiableAt.comp x hf hg


theorem let_rule
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : X → Y → Z) (hf : DifferentiableAt R (fun (xy : X×Y) => f xy.1 xy.2) (x, g x))
  : DifferentiableAt R (fun x => let y := g x; f x y) x := 
by 
  have h : (fun x => let y := g x; f x y) 
           = 
           (fun (xy : X×Y) => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  rw[h]
  apply DifferentiableAt.comp
  apply hf
  apply DifferentiableAt.prod
  apply differentiableAt_id'
  apply hg


theorem pi_rule
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt R (f i) x)
  : DifferentiableAt R (fun x i => f i x) x
  := by apply differentiableAt_pi.2 hf


theorem proj_rule
  (i : ι) (x)
  : DifferentiableAt R (fun x : (i : ι) → E i => x i) x := 
by 
  apply IsBoundedLinearMap.differentiableAt
  apply ContinuousLinearMap.isBoundedLinearMap (fun (x : (i : ι) → E i) =>L[R] x i)


end SciLean.DifferentiableAt


--------------------------------------------------------------------------------
-- Register DiferentiableAt ------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def DifferentiableAt.fpropExt : FPropExt where
  fpropName := ``DifferentiableAt
  getFPropFun? e := 
    if e.isAppOf ``DifferentiableAt then

      if let .some f := e.getArg? 8 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``DifferentiableAt then
      e.modifyArg (fun _ => f) 8 
    else          
      e

  identityRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``DifferentiableAt.id_rule
      origin := .decl ``DifferentiableAt.id_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``DifferentiableAt.const_rule
      origin := .decl ``DifferentiableAt.const_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule e f g := do
    let .some R := e.getArg? 0
      | return none
    let .some x := e.getArg? 9
      | return none


    let HF ← mkAppM ``DifferentiableAt #[R, f, (← mkAppM' g #[x])]
    let .some hf ← FProp.fprop HF
      | trace[Meta.Tactic.fprop.discharge] "Differentiable.comp_rule, failed to discharge hypotheses{HF}"
        return none

    let HG ← mkAppM ``DifferentiableAt #[R, g, x]
    let .some hg ← FProp.fprop HG
      | trace[Meta.Tactic.fprop.discharge] "Differentiable.comp_rule, failed to discharge hypotheses{HG}"
        return none

    mkAppM ``DifferentiableAt.comp_rule #[x,g,hg,f,hf]

  lambdaLetRule e f g := do
    -- let thm : SimpTheorem :=
    -- {
    --   proof  := mkConst ``Differentiable.let_rule 
    --   origin := .decl ``Differentiable.let_rule 
    --   rfl    := false
    -- }
    -- FProp.tryTheorem? e thm (fun _ => pure none)
    let .some R := e.getArg? 0
      | return none
    let .some x := e.getArg? 9
      | return none

    let HF ← mkAppM ``DifferentiableAt #[R, (← mkUncurryFun 2 f), (← mkProdElem #[x, ← mkAppM' g #[x]])]
    let .some hf ← FProp.fprop HF
      | trace[Meta.Tactic.fprop.discharge] "Differentiable.let_rule, failed to discharge hypotheses{HF}"
        return none

    let HG ← mkAppM ``DifferentiableAt #[R, g, x]
    let .some hg ← FProp.fprop HG
      | trace[Meta.Tactic.fprop.discharge] "Differentiable.let_rule, failed to discharge hypotheses{HG}"
        return none

    mkAppM ``DifferentiableAt.let_rule #[x,g,hg,f,hf]

  lambdaLambdaRule e _ :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``DifferentiableAt.pi_rule 
      origin := .decl ``DifferentiableAt.pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  projRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``DifferentiableAt.proj_rule 
      origin := .decl ``DifferentiableAt.proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``DifferentiableAt, DifferentiableAt.fpropExt))


--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean Differentiable 

variable 
  {R : Type _} [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)]


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem id.arg_a.DifferentiableAt_rule (x : X)
  : DifferentiableAt R (id : X → X) x := by simp



-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.DifferentiableAt_rule
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : X → Z) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => (g x, f x)) x
  := DifferentiableAt.prod hg hf


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.DifferentiableAt_rule 
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => (f x).1) x
  := DifferentiableAt.fst hf



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.DifferentiableAt_rule 
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => (f x).2) x
  := DifferentiableAt.snd hf



-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.DifferentiableAt_rule
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : Y → Z) (hf : DifferentiableAt R f (g x))
  : DifferentiableAt R (f ∘ g) x
  := DifferentiableAt.comp x hf hg


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.DifferentiableAt_rule
  (x : X) (f : X → Y) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => - f x) x
  := DifferentiableAt.neg hf
 


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0a1.DifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x)
  : DifferentiableAt R (fun x => f x + g x) x
  := DifferentiableAt.add hf hg
 


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0a1.DifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x)
  : DifferentiableAt R (fun x => f x - g x) x
  := DifferentiableAt.sub hf hg
 

-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0a1.DifferentiableAt_rule
  {Y : Type _} [TopologicalSpace Y] [NormedRing Y] [NormedAlgebra R Y] 
  (x : X) (f g : X → Y) (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x)
  : DifferentiableAt R (fun x => f x * g x) x 
  := DifferentiableAt.mul hf hg


-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HSMul.hSMul.arg_a0a1.DifferentiableAt_rule
  {Y : Type _} [TopologicalSpace Y] [NormedRing Y] [NormedAlgebra R Y] 
  (x : X) (f : X → R) (g : X → Y) (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x)
  : DifferentiableAt R (fun x => f x • g x) x 
  := DifferentiableAt.smul hf hg


-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0a1.DifferentiableAt_rule
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  (x : R) (f : R → K) (g : R → K) 
  (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x) (hx : g x ≠ 0)
  : DifferentiableAt R (fun x => f x / g x) x 
  := DifferentiableAt.div hf hg hx


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.DifferentiableAt_rule
  (n : Nat) (x : X) (f : X → R) (hf : DifferentiableAt R f x) 
  : DifferentiableAt R (fun x => f x ^ n) x
  := DifferentiableAt.pow hf n
