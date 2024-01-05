import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero

import Mathlib.Analysis.Calculus.FDeriv.Basic

import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

namespace SciLean


-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

namespace Continuous

variable 
  {X : Type _} [TopologicalSpace X]
  {Y : Type _} [TopologicalSpace Y]
  {Z : Type _} [TopologicalSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace  (E i)]
  

theorem id_rule
  : Continuous (fun x : X => x)
  := by continuity
  

theorem const_rule (x : X)
  : Continuous (fun _ : Y => x)
  := by continuity


theorem comp_rule
  (g : X → Y) (hg : Continuous g)
  (f : Y → Z) (hf : Continuous f)
  : Continuous (fun x => f (g x))
  := Continuous.comp hf hg


theorem let_rule
  (g : X → Y) (hg : Continuous g)
  (f : X → Y → Z) (hf : Continuous (fun (xy : X×Y) => f xy.1 xy.2))
  : Continuous (fun x => let y := g x; f x y) 
  := by 
  rw[(by rfl : (fun x => let y := g x; f x y) = (fun (xy : X×Y) => f xy.1 xy.2)∘(fun x => (x,g x)))]
  apply (Continuous.comp hf (by continuity))


theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Continuous (f i))
  : Continuous (fun x i => f i x)
  := by continuity

theorem proj_rule
  (i : ι)
  : Continuous (fun x : (i : ι) → E i => x i)
  := by continuity


end SciLean.Continuous


--------------------------------------------------------------------------------
-- Register Continuous ---------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def Continuous.fpropExt : FPropExt where
  fpropName := ``Continuous
  getFPropFun? e := 
    if e.isAppOf ``Continuous then

      if let .some f := e.getArg? 4 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``Continuous then
      e.setArg 4  f
    else          
      e

  identityRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Continuous.id_rule 
      origin := .decl ``Continuous.id_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Continuous.const_rule 
      origin := .decl ``Continuous.const_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule _ f g := do
    let HF ← mkAppM ``Continuous #[f]
    let .some hf ← FProp.fprop HF
      | trace[Meta.Tactic.fprop.discharge] "failed to prove {HF}"
        return none

    let HG ← mkAppM ``Continuous #[g]
    let .some hg ← FProp.fprop HG
      | trace[Meta.Tactic.fprop.discharge] "failed to prove {HG}"
        return none

    mkAppM ``Continuous.comp_rule #[g,hg,f,hf]

  lambdaLetRule _ f g := do

    let HF ← mkAppM ``Continuous #[(← mkUncurryFun 2 f)]
    let .some hf ← FProp.fprop HF
      | trace[Meta.Tactic.fprop.discharge] "failed to prove {HF}"
        return none

    let HG ← mkAppM ``Continuous #[g]
    let .some hg ← FProp.fprop HG
      | trace[Meta.Tactic.fprop.discharge] "failed to prove {HG}"
        return none

    mkAppM ``Continuous.let_rule #[g,hg,f,hf]

  lambdaLambdaRule e _ :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Continuous.pi_rule 
      origin := .decl ``Continuous.pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  projRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``Continuous.proj_rule 
      origin := .decl ``Continuous.proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger _ := return none

-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``Continuous, Continuous.fpropExt))



--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean Continuous 

variable 
  {X : Type _} [TopologicalSpace X]
  {Y : Type _} [TopologicalSpace Y]
  {Z : Type _} [TopologicalSpace Z]
  {R : Type _} [TopologicalSpace R]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace  (E i)]


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fprop]
theorem id.arg_a.Continuous_rule
  : Continuous (fun x : X => id x) := by continuity


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.Continuous_rule
  (g : X → Y) (hg : Continuous g)
  (f : X → Z) (hf : Continuous f)
  : Continuous fun x => (g x, f x)
  := by continuity



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.Continuous_rule 
  (f : X → Y×Z) (hf : Continuous f)
  : Continuous (fun x => (f x).1)
  := Continuous.fst hf



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.Continuous_rule 
  (f : X → Y×Z) (hf : Continuous f)
  : Continuous (fun x => (f x).2)
  := Continuous.snd hf



-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.Continuous_rule
  (f : Y → Z) (hf : Continuous f)
  (g : X → Y) (hg : Continuous g)
  : Continuous (fun x => (f ∘ g) x)
  := Continuous.comp hf hg


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0a1.Continuous_rule
  [Add Y] [ContinuousAdd Y]
  (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous fun x => f x + g x
  := by continuity



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.Continuous_rule
  [Neg Y] [ContinuousNeg Y]
  (f : X → Y) (hf : Continuous f) 
  : Continuous fun x => - f x 
  := by continuity




-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0a1.Continuous_rule
  [Sub Y] [ContinuousSub Y]
  (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous fun x => f x - g x
  := by continuity



-- HMul.hMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0a1.Continuous_rule
  [Mul Y] [ContinuousMul Y]
  (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous (fun x => f x * g x)
  := Continuous.mul hf hg



-- SMul.sMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HSMul.hSMul.arg_a0a1.Continuous_rule
  [SMul R Y] [ContinuousSMul R Y]
  (f : X → R) (g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous (fun x => f x • g x)
  := Continuous.smul hf hg



-- HDiv.hDiv ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 


@[fprop]
def HDiv.hDiv.arg_a0a1.Continuous_rule
  [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K] [HasContinuousInv₀ K]
  (f : R → K) (g : R → K) 
  (hf : Continuous f) (hg : Continuous g) (hx : ∀ x, g x ≠ 0)
  : Continuous (fun x => f x / g x)
  := Continuous.div hf hg hx



-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.Continuous_rule
  {R : Type _} [NontriviallyNormedField R]
  (n : Nat) (f : X → R) (hf : Continuous f) 
  : Continuous (fun x => f x ^ n)
  := Continuous.pow hf n
