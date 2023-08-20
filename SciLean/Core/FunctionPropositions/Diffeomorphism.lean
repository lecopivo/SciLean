import SciLean.Core.FunctionPropositions.Bijective
import SciLean.Core.FunctionPropositions.IsDifferentiable

import SciLean.Core.FunctionTransformations.CDeriv

-- set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [Fintype ι] 
  {E : ι → Type _} [∀ i, Vec K (E i)] 

structure Diffeomorphism (f : X → Y) : Prop where
  bijective : Function.Bijective f 
  differentiable : IsDifferentiable K f 
  locally_diffeo : ∀ x, Function.Bijective (cderiv K f x)

namespace Diffeomorphism

variable (X)
theorem id_rule
  : Diffeomorphism K (fun x : X => x)
  := by sorry_proof
variable {X}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : Diffeomorphism K f) (hg : Diffeomorphism K g)
  : Diffeomorphism K (fun x => f (g x))
  := by sorry_proof



--------------------------------------------------------------------------------
-- Register DiferentiableAt ------------------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``Diffeomorphism
  getFPropFun? e := 
    if e.isAppOf ``Diffeomorphism then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``Diffeomorphism then
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

  constantRule _ := return none
  projRule _ := return none

  compRule e f g := do
    let .some K := e.getArg? 0 | return none

    let thm : SimpTheorem :=
    {
      proof  := ← mkAppM ``comp_rule #[K, f, g]
      origin := .decl ``comp_rule
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  lambdaLetRule _ _ _ := return none
  lambdaLambdaRule _ _ := return none

  discharger e := 
    FProp.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption") e


-- register
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``Diffeomorphism, fpropExt))


end SciLean.Diffeomorphism

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
theorem id.arg_a.Diffeomorphism_rule
  : Diffeomorphism K (id : X → X) := 
by 
  simp[id]; fprop


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.Diffeomorphism_rule
  (f : Y → Z) (g : X → Y) 
  (hf : Diffeomorphism K f) (hg : Diffeomorphism K g)
  : Diffeomorphism K (f ∘ g)
  := by simp[Function.comp]; fprop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Neg.neg.arg_a0.Diffeomorphism_rule
  (f : X → Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => - f x) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; fprop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HAdd.hAdd.arg_a0.Diffeomorphism_rule
  (f : X → Y) (y : Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => f x + y) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; fprop

@[fprop]
theorem HAdd.hAdd.arg_a1.Diffeomorphism_rule
  (y : Y) (f : X → Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => y + f x) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; fprop
 


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem HSub.hSub.arg_a0.Diffeomorphism_rule
  (f : X → Y) (y : Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => f x - y) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; fprop

@[fprop]
theorem HSub.hSub.arg_a1.Diffeomorphism_rule
  (y : Y) (f : X → Y) (hf : Diffeomorphism K f)
  : Diffeomorphism K (fun x => y - f x) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; fprop


-- HMul.hMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HMul.hMul.arg_a0.Diffeomorphism_rule
  (f : X → K) (y : K) (hf : Diffeomorphism K f) (hy : y≠0)
  : Diffeomorphism K (fun x => f x * y) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; simp; fprop

@[fprop]
def HMul.hMul.arg_a1.Diffeomorphism_rule
  (y : K) (f : X → K) (hf : Diffeomorphism K f) (hy : y≠0)
  : Diffeomorphism K (fun x => y * f x) := 
by 
  have ⟨_,_,_⟩ := hf
  constructor
  . fprop
  . fprop
  . ftrans; simp; fprop

#exit
-- TODO: finish up cleaning up the theorems

-- SMul.sMul -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HSMul.hSMul.arg_a0a1.Diffeomorphism_rule
  (f : X → K) (g : X → Y) (hf : Diffeomorphism K f) (hg : Diffeomorphism K g)
  : Diffeomorphism K (fun x => f x • g x)
  := by sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HDiv.hDiv.arg_a0a1.Diffeomorphism_rule
  (f : X → K) (g : X → K)
  (hf : Diffeomorphism K f) (hg : Diffeomorphism K g) (hx : ∀ x, g x ≠ 0)
  : Diffeomorphism K (fun x => f x / g x)
  := by sorry_proof


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
def HPow.hPow.arg_a0.Diffeomorphism_rule
  (n : Nat) (f : X → K) (hf : Diffeomorphism K f) 
  : Diffeomorphism K (fun x => f x ^ n)
  := by sorry_proof



-- Function.invFun -------------------------------------------------------------
-------------------------------------------------------------------------------- 
variable (K)
def Diffeomorphism (f : X → Y) :=
  Function.Bijective f ∧ IsDifferentiable K f ∧  ∀ x, Function.Bijective (cderiv K f x)
variable {K}

open Function in
@[fprop]
theorem Function.invFun.arg_fa1.IsDifferentiable_rule
  (f : X → Y → Z) (g : W → X) (h : W → Z)
  (hf : ∀ x, Diffeomorphism K (f x)) 
  (hf' : IsDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  (hg : IsDifferentiable K g) (hh : IsDifferentiable K h)
  : IsDifferentiable K (fun w : W => invFun (f (g w)) (h w)) := sorry_proof

open Function in
example
  (f : X → Y → Z)
  (hf : ∀ x, Diffeomorphism K (f x)) 
  (hf' : IsDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  : IsDifferentiable K (fun xz : X×Z => invFun (f xz.1) xz.2) := by fprop


open Function in
@[ftrans]
theorem Function.invFun.arg_a1.cderiv_rule 
  (f : Y → Z) (g : X → Z)
  (hf : Diffeomorphism K f) (hg : IsDifferentiable K g)
  : cderiv K (fun x => invFun f (g x))
    =
    fun x dx => 
      let z := g x
      let dz := cderiv K g x dx 
      let y := invFun f z
      let dy := invFun (cderiv K f y) dz
      dy :=
by
  funext x dx
  have H : (cderiv K (f ∘ invFun f) (g x))
           =
           id := by simp[show (f ∘ Function.invFun f) = id from sorry_proof]; ftrans
  have q : cderiv K f (invFun f (g x)) (cderiv K (fun x => invFun f (g x)) x dx) = cderiv K g x dx := sorry
  sorry_proof


open Function in
@[ftrans]
theorem Function.invFun.arg_f.cderiv_rule
  (f : X → Y → Z)
  (hf : ∀ x, Diffeomorphism K (f x)) 
  (hf' : IsDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  : cderiv K (fun x => invFun (f x))
    =
    fun x dx z => 
      let y := invFun (f x) z
      let dfdx_y := (cderiv K f x dx) y
      let df'dy := cderiv K (invFun (f x)) (f x y) (dfdx_y)
      (-df'dy)
  :=
by
  funext x dx
  have H : ((cderiv K (fun x => invFun (f x) ∘ (f x)) x dx) ∘ (invFun (f x)))
           =
           0 := by simp[invFun_comp (hf _).1.1]; ftrans
  rw[← sub_zero (cderiv K (fun x => Function.invFun (f x)) x dx)]
  rw[← H]
  simp_rw[comp.arg_fg.cderiv_rule (K:=K) (fun x => invFun (f x)) f (by fprop) (by fprop)]
  simp[comp]
  funext z
  simp[show f x (invFun (f x) z) = z from sorry_proof]
