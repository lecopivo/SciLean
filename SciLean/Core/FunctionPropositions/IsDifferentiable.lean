import SciLean.Core.Objects.Scalar
import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.Objects.FinVec

import SciLean.Core.FunctionPropositions.IsDifferentiableAt

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [EnumType ι] 
  {E : ι → Type _} [∀ i, Vec K (E i)] 

def IsDifferentiable (f : X → Y) : Prop := ∀ x, IsDifferentiableAt K f x

namespace IsDifferentiable

variable (X)
theorem id_rule
  : IsDifferentiable K (fun x : X => x)
  := by sorry_proof
  

theorem const_rule (y : Y)
  : IsDifferentiable K (fun _ : X => y)
  := by sorry_proof
variable {X}

variable (E)
theorem proj_rule
  (i : ι)
  : IsDifferentiable K (fun x : (i : ι) → E i => x i) := 
by sorry_proof
variable {E}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => f (g x))
  := by sorry_proof


theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : IsDifferentiable K (fun (xy : X×Y) => f xy.1 xy.2))
  (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => let y := g x; f x y) := 
by sorry_proof
  
theorem pi_rule
  (f : (i : ι) → X → E i)
  (hf : ∀ i, IsDifferentiable K (f i))
  : IsDifferentiable K (fun x i => f i x)
  := by sorry_proof



--------------------------------------------------------------------------------
-- Register DiferentiableAt ------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsDifferentiable
  getFPropFun? e := 
    if e.isAppOf ``IsDifferentiable then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsDifferentiable then
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
      proof  := mkConst ``proj_rule 
      origin := .decl ``proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[K, f, g]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``let_rule #[K, f,g]
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

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsDifferentiable, fpropExt))


end SciLean.IsDifferentiable

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, Vec K (E i)] 


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem id.arg_a.IsDifferentiable_rule
  : IsDifferentiable K (fun x : X => id x) := by simp[id]; fprop


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.IsDifferentiable_rule
  (f : Y → Z) (g : X → Y) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => (f ∘ g) x)
  := by sorry_proof


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.IsDifferentiable_rule
  (f : X → Z) (g : X → Y) 
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => (g x, f x))
  := by sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.IsDifferentiable_rule 
  (f : X → Y×Z) (hf : IsDifferentiable K f)
  : IsDifferentiable K (fun x => (f x).1)
  := by sorry_proof



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.IsDifferentiable_rule 
  (f : X → Y×Z) (hf : IsDifferentiable K f)
  : IsDifferentiable K (fun x => (f x).2)
  := by sorry_proof



-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.IsDifferentiable_rule
  (f : X → Y) (hf : IsDifferentiable K f)
  : IsDifferentiable K (fun x => - f x)
  := by sorry_proof
 


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0a1.IsDifferentiable_rule
  (f g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => f x + g x)
  := by sorry_proof
 


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0a1.IsDifferentiable_rule
  (f g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => f x - g x)
  := by sorry_proof
 

-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0a1.IsDifferentiable_rule
  (f g : X → K) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => f x * g x)
  := by sorry_proof


-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HSMul.hSMul.arg_a0a1.IsDifferentiable_rule
  (f : X → K) (g : X → Y) (hf : IsDifferentiable K f) (hg : IsDifferentiable K g)
  : IsDifferentiable K (fun x => f x • g x)
  := by sorry_proof

@[fprop]
theorem HSMul.hSMul.arg_a1.IsDifferentiable_rule_nat
  (c : ℕ) (f : X → Y) (hf : IsDifferentiable K f)
  : IsDifferentiable K fun x => c • f x :=
by
  sorry_proof

@[fprop]
theorem HSMul.hSMul.arg_a1.IsDifferentiable_rule_int
  (c : ℤ) (f : X → Y) (hf : IsDifferentiable K f)
  : IsDifferentiable K fun x => c • f x :=
by
  sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0a1.IsDifferentiable_rule
  (f : X → K) (g : X → K)
  (hf : IsDifferentiable K f) (hg : IsDifferentiable K g) (hx : fpropParam (∀ x, g x ≠ 0))
  : IsDifferentiable K (fun x => f x / g x)
  := by sorry_proof

@[fprop]
def HDiv.hDiv.arg_a0.IsDifferentiable_rule
  (f : X → K) (r : K)
  (hf : IsDifferentiable K f) (hr : fpropParam (r ≠ 0))
  : IsDifferentiable K (fun x => f x / r) := 
by 
  apply HDiv.hDiv.arg_a0a1.IsDifferentiable_rule <;> first | assumption | fprop | simp[hr,fpropParam]


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.IsDifferentiable_rule
  (n : Nat) (f : X → K) (hf : IsDifferentiable K f) 
  : IsDifferentiable K (fun x => f x ^ n)
  := by sorry_proof


-- EnumType.sum ----------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem SciLean.EnumType.sum.arg_f.IsDifferentiable_rule
  (f : X → ι → Y) (hf : ∀ i, IsDifferentiable K (fun x => f x i))
  : IsDifferentiable K (fun x => ∑ i, f x i) :=
by
  sorry_proof

-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.IsDifferentiable_rule
  (c : Prop) [dec : Decidable c] (t e : X → Y)
  (ht : IsDifferentiable K t) (he : IsDifferentiable K e)
  : IsDifferentiable K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]

@[fprop]
theorem dite.arg_te.IsDifferentiable_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → Y) (e : ¬c → X → Y)
  (ht : ∀ h, IsDifferentiable K (t h)) (he : ∀ h, IsDifferentiable K (e h))
  : IsDifferentiable K (fun x => dite c (t · x) (e · x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


--------------------------------------------------------------------------------

section InnerProductSpace

variable 
  {R : Type _} [RealScalar R]
  {X : Type _} [Vec R X]
  {Y : Type _} [SemiHilbert R Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[fprop]
theorem Inner.inner.arg_a0a1.IsDifferentiable_rule
  (f : X → Y) (g : X → Y)
  (hf : IsDifferentiable R f) (hg : IsDifferentiable R g)
  : IsDifferentiable R fun x => ⟪f x, g x⟫[R] :=
by 
  sorry_proof


@[fprop]
theorem SciLean.Norm2.norm2.arg_a0.IsDifferentiable_rule
  (f : X → Y)
  (hf : IsDifferentiable R f) 
  : IsDifferentiable R fun x => ‖f x‖₂²[R] :=
by 
  simp[← SemiInnerProductSpace.inner_norm2]
  fprop


end InnerProductSpace

--------------------------------------------------------------------------------

namespace SciLean
section OnFinVec 


variable 
  {K : Type _} [IsROrC K]
  {IX : Type} [EnumType IX] {X : Type _} [FinVec IX K X]
  {IY : Type} [EnumType IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type} [EnumType IZ] {Z : Type _} [FinVec IZ K Z]

@[fprop]
theorem Basis.proj.arg_x.IsDifferentiable_rule (i : IX)
  : IsDifferentiable K (fun x : X => ℼ i x) := by sorry_proof

@[fprop]
theorem DualBasis.dualProj.arg_x.IsDifferentiable_rule (i : IX)
  : IsDifferentiable K (fun x : X => ℼ' i x) := by sorry_proof

@[fprop]
theorem BasisDuality.toDual.arg_x.IsDifferentiable_rule
  : IsDifferentiable K (fun x : X => BasisDuality.toDual x) := by sorry_proof

@[fprop]
theorem BasisDuality.fromDual.arg_x.IsDifferentiable_rule
  : IsDifferentiable K (fun x : X => BasisDuality.fromDual x) := by sorry_proof

end OnFinVec
end SciLean
