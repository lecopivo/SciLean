import SciLean.Core.FunctionPropositions.IsDifferentiable
import SciLean.Core.FunctionPropositions.HasSemiAdjoint
import SciLean.Core.FunctionPropositions.HasAdjDiffAt

import SciLean.Core.FunctionTransformations.CDeriv

import Lean.Meta.Tactic.Assumption

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

def HasAdjDiff (f : X → Y)  : Prop := IsDifferentiable K f ∧ ∀ x, HasSemiAdjoint K (cderiv K f x)

namespace HasAdjDiff

variable (X)
theorem id_rule
  : HasAdjDiff K (fun x : X => x) := 
by 
  constructor; fprop; ftrans; fprop

theorem const_rule (y : Y)
  : HasAdjDiff K (fun _ : X => y) := 
by 
  constructor; fprop; ftrans; fprop

variable {X}

variable (E)
theorem proj_rule
  (i : ι)
  : HasAdjDiff K (fun x : (i : ι) → E i => x i) := 
by 
  constructor; fprop; ftrans; fprop

variable {E}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => f (g x)) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop

theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2))
  (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => let y := g x; f x y) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop
  
theorem pi_rule
  (f : (i : ι) → X → E i)
  (hf : ∀ i, HasAdjDiff K (f i))
  : HasAdjDiff K (fun x i => f i x) := 
by 
  have := fun i => (hf i).1
  have := fun i => (hf i).2
  constructor; fprop; ftrans; fprop


--------------------------------------------------------------------------------
-- Register HadAdjDiff ---------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``HasAdjDiff
  getFPropFun? e := 
    if e.isAppOf ``HasAdjDiff then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``HasAdjDiff then
      e.setArg 6  f
    else          
      e

  identityRule    e := do
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``id_rule
      origin := .decl ``id_rule
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
      proof  := mkConst ``HasAdjDiff.proj_rule 
      origin := .decl ``HasAdjDiff.proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[K,f,g]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``let_rule #[K,f,g]
      origin := .decl ``let_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLambdaRule e _ :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``pi_rule 
      origin := .decl ``pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger e := do
    if let .some prf ← Lean.Meta.findLocalDeclWithType? e then
      return .some (.fvar prf)
    else
      if e.isAppOf ``fpropParam then
        trace[Meta.Tactic.fprop.unsafe] s!"discharging with sorry: {← ppExpr e}"
        return .some <| ← mkAppOptM ``sorryProofAxiom #[e.appArg!]
      else
        return none


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``HasAdjDiff, fpropExt))


end SciLean.HasAdjDiff

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)] 


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem id.arg_a.HasAdjDiff_rule (x : X)
  : HasAdjDiff K (fun x : X => id x) := by constructor; fprop; ftrans; fprop


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.HasAdjDiff_rule
  (g : X → Y) (hg : HasAdjDiff K g)
  (f : X → Z) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => (g x, f x)) := 
by 
  have ⟨_,_⟩ := hg
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.HasAdjDiff_rule 
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => (f x).1) := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.HasAdjDiff_rule 
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => (f x).2) := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- cderiv ----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem SciLean.cderiv.arg_dx.HasSemiAdjoint_rule
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : HasAdjDiff K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K fun dx => cderiv K f y (g dx) :=
by
  apply HasSemiAdjoint.comp_rule K (cderiv K f y) g (hf.2 y) hg


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.HasAdjDiff_rule
  (g : X → Y) (hg : HasAdjDiff K g)
  (f : Y → Z) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => (f ∘ g) x) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.HasAdjDiff_rule
  (f : X → Y) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => - f x) := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0a1.HasAdjDiff_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => f x + g x) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0a1.HasAdjDiff_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => f x - g x) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop
 

-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0a1.HasAdjDiff_rule
  (f g : X → K) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => f x * g x) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate in
@[fprop]
theorem HSMul.hSMul.arg_a1.HasAdjDiff_rule
  (c : K) (g : X → Y) (x : X) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => c • g x) :=
by 
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


open ComplexConjugate in
@[fprop]
theorem HSMul.hSMul.arg_a0a1.HasAdjDiff_rule
  {Y : Type _} [SemiHilbert K Y]
  (f : X → K) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : HasAdjDiff K (fun x => f x • g x) :=
by 
  have ⟨_,_⟩ := hg
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0a1.HasAdjDiff_rule
  (f : X → K) (g : X → K) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : HasAdjDiff K (fun x => f x / g x) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.HasAdjDiff_rule
  (n : Nat) (f : X → K) (hf : HasAdjDiff K f)
  : HasAdjDiff K (fun x => f x ^ n) := 
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem SciLean.EnumType.sum.arg_f.HasAdjDiff_rule
  (f : X → ι → Y) (hf : ∀ i, HasAdjDiff K (f · i))
  : HasAdjDiff K (fun x => ∑ i, f x i) :=
by
  have := fun i => (hf i).1
  constructor; fprop; ftrans; fprop

-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.HasAdjDiff_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  (ht : HasAdjDiff K t) (he : HasAdjDiff K e)
  : HasAdjDiff K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]

@[fprop]
theorem dite.arg_te.HasAdjDiff_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → Y) (e : ¬c → X → Y)
  (ht : ∀ h, HasAdjDiff K (t h)) (he : ∀ h, HasAdjDiff K (e h))
  : HasAdjDiff K (fun x => dite c (t · x) (e · x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]



--------------------------------------------------------------------------------

section InnerProductSpace

variable 
  {R : Type _} [RealScalar R]
  {X : Type _} [SemiInnerProductSpace R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[fprop]
theorem Inner.inner.arg_a0a1.HasAdjDiff_rule
  (f : X → Y) (g : X → Y)
  (hf : HasAdjDiff R f) (hg : HasAdjDiff R g)
  : HasAdjDiff R fun x => ⟪f x, g x⟫[R] :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  constructor; fprop; ftrans; fprop

@[fprop]
theorem SciLean.Norm2.norm2.arg_a0.HasAdjDiff_rule
  (f : X → Y)
  (hf : HasAdjDiff R f)
  : HasAdjDiff R fun x => ‖f x‖₂²[R] :=
by 
  have ⟨_,_⟩ := hf
  constructor; fprop; ftrans; fprop


@[fprop]
theorem SciLean.norm₂.arg_x.HasAdjDiff_rule
  (f : X → Y)
  (hf : HasAdjDiff R f) (hfz : fpropParam <| ∀ x, f x ≠ 0)
  : HasAdjDiff R fun x => ‖f x‖₂[R] :=
by 
  have ⟨_,_⟩ := hf
  constructor; sorry_proof; sorry_proof


end InnerProductSpace


-- semiAdjoint -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem SciLean.semiAdjoint.arg_y.IsDifferentiable_rule {W : Type _} [Vec K W]
  (f : X → Y) (a0 : W → Y) (ha0 : IsDifferentiable K a0)
  : IsDifferentiable K (fun w => semiAdjoint K f (a0 w)) := 
by
  unfold semiAdjoint
  match Classical.dec (HasSemiAdjoint K f) with
  | isTrue h => sorry_proof -- TODO: f† exists and is smooth linear map
  | isFalse h => simp[h]; fprop

@[fprop]
theorem SciLean.semiAdjoint.arg_y.HasAdjDiff_rule
  (f : X → Y) (a0 : W → Y) (ha0 : HasAdjDiff K a0)
  : HasAdjDiff K (fun w => semiAdjoint K f (a0 w)) := 
by
  unfold semiAdjoint
  match Classical.dec (HasSemiAdjoint K f) with
  | isTrue h => sorry_proof -- TODO: f† exists and is smooth linear map
  | isFalse h => simp[h]; fprop




