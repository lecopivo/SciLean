import SciLean.Core.FunctionPropositions.IsDifferentiableAt
import SciLean.Core.FunctionPropositions.HasSemiAdjoint

import SciLean.Core.FunctionTransformations.CDeriv

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [Fintype ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)] 

def HasAdjDiffAt (f : X → Y) (x : X) : Prop :=
  IsDifferentiableAt K f x ∧ 
  HasSemiAdjoint K (cderiv K f x)

namespace HasAdjDiffAt

variable (X)
theorem id_rule (x : X)
  : HasAdjDiffAt K (fun x : X => x) x := 
by 
  constructor; fprop; ftrans; fprop
  
theorem const_rule (y : Y) (x : X)
  : HasAdjDiffAt K (fun _ : X => y) x := 
by 
  constructor; fprop; ftrans; fprop

variable {X}

variable (E)
theorem proj_rule
  (i : ι) (x)
  : HasAdjDiffAt K (fun x : (i : ι) → E i => x i) x := 
by 
  constructor; fprop; ftrans; fprop

variable {E}

theorem comp_rule
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt K f (g x)) (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => f (g x)) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop

theorem let_rule
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x))
  (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => let y := g x; f x y) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop
  
theorem pi_rule
  (f : (i : ι) → X → E i) (x : X)
  (hf : ∀ i, HasAdjDiffAt K (f i) x)
  : HasAdjDiffAt K (fun x i => f i x) x := 
by 
  have := fun i => (hf i).1
  have := fun i => (hf i).2
  constructor; fprop; ftrans; fprop


--------------------------------------------------------------------------------
-- Register DiferentiableAt ------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``HasAdjDiffAt
  getFPropFun? e := 
    if e.isAppOf ``HasAdjDiffAt then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``HasAdjDiffAt then
      e.modifyArg (fun _ => f) 6 
    else          
      e

  identityRule    e := do
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``id_rule
      origin := .decl ``HasAdjDiffAt.id_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``const_rule
      origin := .decl ``const_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  projRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``HasAdjDiffAt.proj_rule 
      origin := .decl ``HasAdjDiffAt.proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some x := e.getArg? 7 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[K,f,g,x]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule e f g := do
    let .some K := e.getArg? 0 | return none
    let .some x := e.getArg? 7 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``let_rule #[K,f,g,x]
      origin := .decl ``let_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLambdaRule e _ :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``HasAdjDiffAt.pi_rule 
      origin := .decl ``HasAdjDiffAt.pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``HasAdjDiffAt, HasAdjDiffAt.fpropExt))


end SciLean.HasAdjDiffAt

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [Fintype ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)] 


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem id.arg_a.HasAdjDiffAt_rule (x : X)
  : HasAdjDiffAt K (id : X → X) x := by constructor; fprop; ftrans; fprop


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.HasAdjDiffAt_rule
  (x : X)
  (g : X → Y) (hg : HasAdjDiffAt K g x)
  (f : X → Z) (hf : HasAdjDiffAt K f x)
  : HasAdjDiffAt K (fun x => (g x, f x)) x := 
by 
  have ⟨_,_⟩ := hg
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.HasAdjDiffAt_rule 
  (x : X)
  (f : X → Y×Z) (hf : HasAdjDiffAt K f x)
  : HasAdjDiffAt K (fun x => (f x).1) x := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.HasAdjDiffAt_rule 
  (x : X)
  (f : X → Y×Z) (hf : HasAdjDiffAt K f x)
  : HasAdjDiffAt K (fun x => (f x).2) x := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- cderiv ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem SciLean.cderiv.arg_dx.HasSemiAdjoint_rule_at
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : HasAdjDiffAt K f y) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K fun dx => cderiv K f y (g dx) :=
by
  apply HasSemiAdjoint.comp_rule K (cderiv K f y) g hf.2 hg


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.HasAdjDiffAt_rule
  (x : X)
  (g : X → Y) (hg : HasAdjDiffAt K g x)
  (f : Y → Z) (hf : HasAdjDiffAt K f (g x))
  : HasAdjDiffAt K (f ∘ g) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.HasAdjDiffAt_rule
  (x : X) (f : X → Y) (hf : HasAdjDiffAt K f x)
  : HasAdjDiffAt K (fun x => - f x) x := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0a1.HasAdjDiffAt_rule
  (x : X) (f g : X → Y) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => f x + g x) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0a1.HasAdjDiffAt_rule
  (x : X) (f g : X → Y) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => f x - g x) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop
 

-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0a1.HasAdjDiffAt_rule
  (x : X) (f g : X → K) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => f x * g x) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate in
@[fprop]
theorem HSMul.hSMul.arg_a1.HasAdjDiffAt_rule
  (c : K) (g : X → Y) (x : X) (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => c • g x) x :=
by 
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop



@[fprop]
def HSMul.hSMul.arg_a0a1.HasAdjDiffAt_rule
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (x : X) (f : X → K) (g : X → Y) 
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : HasAdjDiffAt K (fun x => f x • g x) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0a1.HasAdjDiffAt_rule
  (x : X) (f : X → K) (g : X → K) 
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) (hx : g x ≠ 0)
  : HasAdjDiffAt K (fun x => f x / g x) x := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.HasAdjDiffAt_rule
  (n : Nat) (x : X) (f : X → K) (hf : HasAdjDiffAt K f x) 
  : HasAdjDiffAt K (fun x => f x ^ n) x := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop



--------------------------------------------------------------------------------

section InnerProductSpace

variable 
  {R : Type} [RealScalar R]
  {X : Type} [SemiInnerProductSpace R X]
  {Y : Type} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[fprop]
theorem Inner.inner.arg_a0a1.HasAdjDiffAt_rule
  (f : X → Y) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hg : HasAdjDiffAt R g x)
  : HasAdjDiffAt R (fun x => ⟪f x, g x⟫[R]) x :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


@[fprop]
theorem SciLean.Norm2.norm2.arg_a0.HasAdjDiffAt_rule
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x)
  : HasAdjDiffAt R (fun x => ‖f x‖₂²[R]) x :=
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop

@[fprop]
theorem SciLean.norm₂.arg_a0.HasAdjDiffAt_rule
  (f : X → Y) (x : X)
  (hf : HasAdjDiffAt R f x) (hx : f x≠0)
  : HasAdjDiffAt R (fun x => ‖f x‖₂[R]) x :=
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


end InnerProductSpace
