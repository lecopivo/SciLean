import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.FunctionPropositions.IsLinearMap
import SciLean.Core.Simp

set_option linter.unusedVariables false

namespace SciLean

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [EnumType ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)] 

def HasSemiAdjoint (f : X → Y) : Prop :=
   ∃ f' : Y → X, 
     ∀ x y, TestFunction x → ⟪y, f x⟫[K] = ⟪f' y, x⟫[K]
   -- at some point I was convinced that these conditions are important
   -- maybe add: ∀ x, TestFunction x → TestFunction (f x) - I think this is important for proving linearity of f'
   -- maybe add: ∀ y, TestFunction y → TestFunction (f' y)

/-- Generalization of adjoint of linear map `f : X → Y`.

If `f : X → Y` is linear map between Hilbert spaces then `semiAdjoint K f = adjoint K f`.

`semiAdjoint` is a generalization of adjoint to spaces that are not necessarily complete 
and might have inner product defined only on a dense subset, see `SemiInnerProductSpace`
for more information.
 -/
noncomputable
def semiAdjoint (f : X → Y) (y : Y) : X :=
  match Classical.dec (HasSemiAdjoint K f) with
  | isTrue h => Classical.choose h y
  | isFalse _ => 0

-- Basic identities ------------------------------------------------------------
--------------------------------------------------------------------------------

-- there should be a command to generate these push/pull  theorems
@[neg_pull]
theorem semiAdjoint.arg_y.neg_pull 
  (f : X → Y) (y : Y)
  : semiAdjoint K f (-y)
    =
    - semiAdjoint K f y := sorry_proof

@[neg_push]
theorem semiAdjoint.arg_y.neg_push 
  (f : X → Y) (y : Y)
  : - semiAdjoint K f y
    =
    semiAdjoint K f (-y) := sorry_proof

@[add_pull]
theorem semiAdjoint.arg_y.add_pull 
  (f : X → Y) (y y : Y)
  : semiAdjoint K f (y+y')
    =
    semiAdjoint K f y + semiAdjoint K f y' := sorry_proof

@[add_push]
theorem semiAdjoint.arg_y.add_push
  (f : X → Y) (y y' : Y)
  : semiAdjoint K f y + semiAdjoint K f y'
    =
    semiAdjoint K f (y+y') := sorry_proof

@[sub_pull]
theorem semiAdjoint.arg_y.sub_pull 
  (f : X → Y) (y y' : Y)
  : semiAdjoint K f (y-y')
    =
    semiAdjoint K f y - semiAdjoint K f y' := sorry_proof

@[sub_push]
theorem semiAdjoint.arg_y.sub_push
  (f : X → Y) (y : Y)
  : semiAdjoint K f y - semiAdjoint K f y'
    =
    semiAdjoint K f (y-y') := sorry_proof

@[smul_pull]
theorem semiAdjoint.arg_y.smul_pull 
  (f : X → Y) (y : Y) (k : K)
  : semiAdjoint K f (k•y)
    =
    k • semiAdjoint K f y := sorry_proof

@[smul_push]
theorem semiAdjoint.arg_y.smul_push 
  (f : X → Y) (y : Y) (k : K)
  : k • semiAdjoint K f y
    =
    semiAdjoint K f (k•y) := sorry_proof

@[simp, ftrans_simp]
theorem semiAdjoint.arg_y.zero
  (f : X → Y)
  : semiAdjoint K f 0 = 0 := by sorry_proof


def semi_inner_ext (x x' : X)
  : (∀ φ, TestFunction φ → ⟪x, φ⟫[K] = ⟪x', φ⟫[K])
    →
    x = x' := sorry_proof

theorem semiAdjoint_choose {f : X → Y} (hf : HasSemiAdjoint K f)
  : semiAdjoint K f = Classical.choose hf := sorry_proof

def semiAdjoint_unique (f : X → Y) (hf : HasSemiAdjoint K f)
  (f' : Y → X) (hf' : ∀ x y, TestFunction x → ⟪y, f x⟫[K] = ⟪f' y, x⟫[K])
  : f' = semiAdjoint K f :=
by
  funext y
  apply semi_inner_ext K
  intro φ hφ
  rw[← hf' φ y hφ]
  rw[semiAdjoint_choose _ hf]
  rw[← Classical.choose_spec hf φ y hφ]


-- Lambda calculus rules -------------------------------------------------------
--------------------------------------------------------------------------------

namespace HasSemiAdjoint 


variable (X)
theorem id_rule
  : HasSemiAdjoint K (fun x : X => x) := 
by 
  apply Exists.intro (fun x => x) _
  simp
  
theorem const_rule 
  : HasSemiAdjoint K (fun _ : X => (0:Y)) := 
by 
  apply Exists.intro (fun _ => 0) _
  simp; sorry_proof
variable {X}

variable (E)
theorem proj_rule 
  (i : ι)
  : HasSemiAdjoint K (fun x : (i : ι) → E i => x i) := 
by 
  apply Exists.intro (fun (y : E i) j => if h : i=j then h▸y else 0) _
  sorry_proof
variable {E}

theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K (fun x => f (g x)) := 
by 
  apply Exists.intro (fun z => semiAdjoint K g (semiAdjoint K f z)) _
  sorry_proof

theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : HasSemiAdjoint K (fun (xy : X×Y) => f xy.1 xy.2))
  (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K (fun x => let y := g x; f x y) := 
by 
  apply Exists.intro (fun z => semiAdjoint K (fun x => (x, g x)) (semiAdjoint K (fun (xy : X×Y) => f xy.1 xy.2) z)) _
  sorry_proof
  
theorem pi_rule
  (f : (i : ι) → X → E i)
  (hf : ∀ i, HasSemiAdjoint K (f i))
  : HasSemiAdjoint K (fun x i => f i x) := 
by 
  -- apply Exists.intro (fun g => ∑ i, semiAdjoint K (f i) (g i)) _
  sorry_proof

--------------------------------------------------------------------------------
-- Register HasSemiAdjoint ----------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``HasSemiAdjoint
  getFPropFun? e := 
    if e.isAppOf ``HasSemiAdjoint then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``HasSemiAdjoint then
      e.setArg 6 f
    else          
      e

  identityRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``id_rule 
      origin := .decl ``id_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule e := 
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
      proof  := ← mkAppM ``comp_rule #[K, f,g]
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
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``HasSemiAdjoint, fpropExt))

end SciLean.HasSemiAdjoint

--------------------------------------------------------------------------------

open SciLean HasSemiAdjoint ContinuousLinearMap

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
theorem id.arg_a.HasSemiAdjoint_rule
  : HasSemiAdjoint K (fun x : X => id x) := by sorry_proof


-- Function.comp ---------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Function.comp.arg_a0.HasSemiAdjoint_rule
  (f : Y → Z) (g : X → Y)
  (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K (fun x : X => (f ∘ g) x) :=
by
  unfold Function.comp; fprop


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.HasSemiAdjoint_rule
  (g : X → Y) (hg : HasSemiAdjoint K g)
  (f : X → Z) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => (g x, f x) := 
by sorry_proof


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.HasSemiAdjoint_rule
  (f : X → Y×Z) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun (x : X) => (f x).fst := 
by sorry_proof


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.HasSemiAdjoint_rule
  (f : X → Y×Z) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun (x : X) => (f x).snd := 
by sorry_proof


-- Neg.neg ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem Neg.neg.arg_a0.HasSemiAdjoint_rule 
  (f : X → Y)
  : HasSemiAdjoint K fun x => - f x := 
by sorry_proof


-- HAdd.hAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HAdd.hAdd.arg_a0a1.HasSemiAdjoint_rule [ContinuousAdd Y]
  (f g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K fun x => f x + g x := 
by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSub.hSub.arg_a0a1.HasSemiAdjoint_rule 
  (f g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g)
  : HasSemiAdjoint K fun x => f x - g x := 
by sorry_proof


-- HMul.hMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HMul.hMul.arg_a0.HasSemiAdjoint_rule
  (f : X → K) (y' : K) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => f x * y' := 
by sorry_proof

@[fprop]
theorem HMul.hMul.arg_a1.HasSemiAdjoint_rule
  (y' : K) (f : X → K) (hf : HasSemiAdjoint K f)   
  : HasSemiAdjoint K fun x => y' * f x := 
by sorry_proof


-- Smul.smul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSMul.hSMul.arg_a0.HasSemiAdjoint_rule
  {Y : Type _} [SemiHilbert K Y]
  (f : X → K) (y : Y) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => f x • y := 
by 
  apply Exists.intro (fun (y' : Y) => ⟪y,y'⟫[K] • semiAdjoint K f 1) _
  sorry_proof

open ComplexConjugate in
@[fprop]
theorem HSMul.hSMul.arg_a1.HasSemiAdjoint_rule 
  (c : K) (f : X → Y) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => c • f x := 
by 
  apply Exists.intro (fun (y' : Y) => conj c • semiAdjoint K f y') _
  sorry_proof



-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate in
@[fprop]
theorem HDiv.hDiv.arg_a0.HasSemiAdjoint_rule
  (f : X → K) (hf : HasSemiAdjoint K f) (y : K) 
  : HasSemiAdjoint K fun x => f x / y := 
by 
  apply Exists.intro (fun (y' : K) => (1/conj y) • semiAdjoint K f y') _
  sorry_proof


-- Finset.sum -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open BigOperators in
@[fprop]
theorem Finset.sum.arg_f.HasSemiAdjoint_rule {ι : Type _} [Fintype ι]
  (f : X → ι → Y) (_ : ∀ i, HasSemiAdjoint K fun x : X => f x i) (A : Finset ι)
  : HasSemiAdjoint K fun x => ∑ i in A, f x i := 
by 
  unfold HasSemiAdjoint
  apply Exists.intro (fun (y' : Y) => ∑ i in A, semiAdjoint K (f · i) y' ) _
  sorry_proof

-- EnumType.sum -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem SciLean.EnumType.sum.arg_f.HasSemiAdjoint_rule
  (f : X → ι → Y) (hf : ∀ i, HasSemiAdjoint K fun x : X => f x i)
  : HasSemiAdjoint K fun x => ∑ i, f x i := 
by 
  -- unfold HasSemiAdjoint
  -- apply Exists.intro (fun (y' : Y) => ∑ i, semiAdjoint K (f · i) y') _
  sorry_proof


-- do we need this one?
-- open BigOperators in
-- @[fprop]
-- theorem Finset.sum.arg_f.HasSemiAdjoint_rule'
--   (f : ι → X → Y) (hf : ∀ i, HasSemiAdjoint K (f i)) (A : Finset ι)
--   : HasSemiAdjoint K fun (x : X) => ∑ i in A, f i x := sorry_proof

-- conj/starRingEnd ------------------------------------------------------------
-------------------------------------------------------------------------------- 

set_option linter.fpropDeclName false in
open ComplexConjugate in
@[fprop]
theorem starRingEnd.arg_a.HasSemiAdjoint_rule
  (f : X → K) (_ : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => conj (f x) :=
by
  sorry_proof


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.HasSemiAdjoint_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : HasSemiAdjoint K t) (he : HasSemiAdjoint K e)
  : HasSemiAdjoint K fun x => ite c (t x) (e x) := 
by
  induction dec
  case isTrue h  => simp[h]; fprop
  case isFalse h => simp[h]; fprop


@[fprop]
theorem dite.arg_te.HasSemiAdjoint_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, HasSemiAdjoint K (t p)) 
  (e : ¬c → X → Y) (he : ∀ p, HasSemiAdjoint K (e p))
  : HasSemiAdjoint K fun x => dite c (t · x) (e · x) := 
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he


-------------------------------------------------------------------------------- 

section InnerProductSpace

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiHilbert K Y]

-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open ComplexConjugate

@[fprop]
theorem Inner.inner.arg_a0.HasSemiAdjoint_rule
  (f : X → Y) (_ : HasSemiAdjoint K f) (y : Y)
  : HasSemiAdjoint K fun x => ⟪f x, y⟫[K] :=
by 
  apply Exists.intro (fun (c : K) => (conj c) • semiAdjoint K f y) _
  sorry_proof

@[fprop]
theorem Inner.inner.arg_a1.HasSemiAdjoint_rule
  (f : X → Y) (_ : HasSemiAdjoint K f) (y : Y)
  : HasSemiAdjoint K fun x => ⟪y, f x⟫[K] :=
by 
  apply Exists.intro (fun (c : K) => c • semiAdjoint K f y) _
  sorry_proof


end InnerProductSpace


-- semiAdjoint -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem SciLean.semiAdjoint.arg_y.HasSemiAdjoint_rule
  (f : X → Y) (a0 : W → Y) (ha0 : HasSemiAdjoint K a0)
  : HasSemiAdjoint K (fun w => semiAdjoint K f (a0 w)) :=
by
  -- either `f` has semiadjoint then the total adjoint id `a0† f†`
  -- or `f` does not have semiadjoint and `f†` is zero thus map and that has adjoint
  sorry_proof


