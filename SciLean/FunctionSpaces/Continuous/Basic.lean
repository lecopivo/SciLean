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


end SciLean.Continuous


--------------------------------------------------------------------------------
-- Register Diferentiable ------------------------------------------------------
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
      e.modifyArg (fun _ => f) 4 
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
    -- let thm : SimpTheorem :=
    -- {
    --   proof  := mkConst ``Continuous.let_rule 
    --   origin := .decl ``Continuous.let_rule 
    --   rfl    := false
    -- }
    -- FProp.tryTheorem? e thm (fun _ => pure none)

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


@[fprop_rule]
theorem id.arg_a.Continuous
  : Continuous (id : X → X) := by continuity


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem Prod.mk.arg_fstsnd.Continuous_comp
  (g : X → Y) (hg : Continuous g)
  (f : X → Z) (hf : Continuous f)
  : Continuous fun x => (g x, f x)
  := by continuity



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem Prod.fst.arg_self.Continuous_comp 
  (f : X → Y×Z) (hf : Continuous f)
  : Continuous (fun x => (f x).1)
  := Continuous.fst hf



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem Prod.snd.arg_self.Continuous_comp 
  (f : X → Y×Z) (hf : Continuous f)
  : Continuous (fun x => (f x).2)
  := Continuous.snd hf



-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem Function.comp.arg_x.Continuous_comp
  (f : Y → Z) (hf : Continuous f)
  (g : X → Y) (hg : Continuous g)
  : Continuous (f ∘ g)
  := Continuous.comp hf hg



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem Neg.neg.arg_a2.Continuous_comp
  [Neg Y] [ContinuousNeg Y]
  (f : X → Y) (hf : Continuous f) 
  : Continuous fun x => - f x 
  := by continuity



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem HAdd.hAdd.arg_a4a5.Continuous_comp
  [Add Y] [ContinuousAdd Y]
  (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous fun x => f x + g x
  := by continuity



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop_rule]
theorem HSub.hSub.arg_a4a5.Continuous_comp
  [Sub Y] [ContinuousSub Y]
  (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous fun x => f x - g x
  := by continuity



-- HMul.hMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop_rule]
def HMul.hMul.arg_a4a5.Continuous_comp
  [Mul Y] [ContinuousMul Y]
  (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous (fun x => f x * g x)
  := Continuous.mul hf hg



-- SMul.sMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop_rule]
def SMul.sMul.arg_a4a5.Continuous_comp
  [SMul R Y] [ContinuousSMul R Y]
  (f : X → R) (g : X → Y) (hf : Continuous f) (hg : Continuous g)
  : Continuous (fun x => f x • g x)
  := Continuous.smul hf hg



-- HDiv.hDiv ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 


@[fprop_rule]
def HDiv.hDiv.arg_a4a5.Continuous_comp
  [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K] [HasContinuousInv₀ K]
  (f : R → K) (g : R → K) 
  (hf : Continuous f) (hg : Continuous g) (hx : ∀ x, g x ≠ 0)
  : Continuous (fun x => f x / g x)
  := Continuous.div hf hg hx



