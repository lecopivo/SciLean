import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.Core.Objects.Vec

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [Fintype ι] 
  {E : ι → Type _} [∀ i, Vec K (E i)] 

def IsDifferentiableAt (f : X → Y) (x : X) : Prop :=
  ∀ (c : K → X),
      c 0 = x 
      → 
      Curve.DifferentiableAt c 0
      →
      Curve.DifferentiableAt (f∘c) 0


namespace IsDifferentiableAt

variable (X)
theorem id_rule (x : X)
  : IsDifferentiableAt K (fun x : X => x) x
  := by sorry_proof
  

theorem const_rule (y : Y) (x : X)
  : IsDifferentiableAt K (fun _ : X => y) x
  := by sorry_proof
variable {X}

variable (E)
theorem proj_rule
  (i : ι) (x)
  : IsDifferentiableAt K (fun x : (i : ι) → E i => x i) x := 
by sorry_proof
variable {E}

theorem comp_rule
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : IsDifferentiableAt K f (g x)) (hg : IsDifferentiableAt K g x)
  : IsDifferentiableAt K (fun x => f (g x)) x
  := by sorry_proof


theorem let_rule
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : IsDifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x))
  (hg : IsDifferentiableAt K g x)
  : IsDifferentiableAt K (fun x => let y := g x; f x y) x := 
by sorry_proof
  
theorem pi_rule
  (f : (i : ι) → X → E i) (x : X)
  (hf : ∀ i, IsDifferentiableAt K (f i) x)
  : IsDifferentiableAt K (fun x i => f i x) x
  := by sorry_proof



--------------------------------------------------------------------------------
-- Register DiferentiableAt ------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsDifferentiableAt
  getFPropFun? e := 
    if e.isAppOf ``IsDifferentiableAt then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsDifferentiableAt then
      e.modifyArg (fun _ => f) 6 
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
      proof  := mkConst ``IsDifferentiableAt.pi_rule 
      origin := .decl ``IsDifferentiableAt.pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsDifferentiableAt, fpropExt))


end SciLean.IsDifferentiableAt

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [Fintype ι] 
  {E : ι → Type _} [∀ i, Vec K (E i)] 


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem id.arg_a.IsDifferentiableAt_rule (x : X)
  : IsDifferentiableAt K (id : X → X) x := by sorry_proof



-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.IsDifferentiableAt_rule
  (x : X)
  (g : X → Y) (hg : IsDifferentiableAt K g x)
  (f : X → Z) (hf : IsDifferentiableAt K f x)
  : IsDifferentiableAt K (fun x => (g x, f x)) x
  := by sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.IsDifferentiableAt_rule 
  (x : X)
  (f : X → Y×Z) (hf : IsDifferentiableAt K f x)
  : IsDifferentiableAt K (fun x => (f x).1) x
  := by sorry_proof



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.IsDifferentiableAt_rule 
  (x : X)
  (f : X → Y×Z) (hf : IsDifferentiableAt K f x)
  : IsDifferentiableAt K (fun x => (f x).2) x
  := by sorry_proof



-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.IsDifferentiableAt_rule
  (x : X)
  (g : X → Y) (hg : IsDifferentiableAt K g x)
  (f : Y → Z) (hf : IsDifferentiableAt K f (g x))
  : IsDifferentiableAt K (f ∘ g) x
  := by sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.IsDifferentiableAt_rule
  (x : X) (f : X → Y) (hf : IsDifferentiableAt K f x)
  : IsDifferentiableAt K (fun x => - f x) x
  := by sorry_proof
 


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0a1.IsDifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : IsDifferentiableAt K (fun x => f x + g x) x
  := by sorry_proof
 


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0a1.IsDifferentiableAt_rule
  (x : X) (f g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : IsDifferentiableAt K (fun x => f x - g x) x
  := by sorry_proof
 

-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0a1.IsDifferentiableAt_rule
  (x : X) (f g : X → K) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : IsDifferentiableAt K (fun x => f x * g x) x 
  := by sorry_proof


-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HSMul.hSMul.arg_a0a1.IsDifferentiableAt_rule
  (x : X) (f : X → K) (g : X → Y) (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x)
  : IsDifferentiableAt K (fun x => f x • g x) x 
  := by sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0a1.IsDifferentiableAt_rule
  (x : X) (f : X → K) (g : X → K) 
  (hf : IsDifferentiableAt K f x) (hg : IsDifferentiableAt K g x) (hx : g x ≠ 0)
  : IsDifferentiableAt K (fun x => f x / g x) x 
  := by sorry_proof


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.IsDifferentiableAt_rule
  (n : Nat) (x : X) (f : X → K) (hf : IsDifferentiableAt K f x) 
  : IsDifferentiableAt K (fun x => f x ^ n) x
  := by sorry_proof
