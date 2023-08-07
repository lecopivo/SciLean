import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

import SciLean.Tactic.FProp.Basic
import SciLean.Tactic.FProp.Notation

namespace SciLean


variable (R : Type _) [Semiring R]
    {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
    {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]


structure IsContinuousLinearMap (f : X → Y) : Prop where
  map_add' : ∀ x y, f (x + y) = f x + f y
  map_smul' : ∀ (r : R) (x : X), f (r • x) = r • f x
  cont : Continuous f := by continuity


-- Lambda function notation ----------------------------------------------------
--------------------------------------------------------------------------------


def ContinuousLinearMap.mk'
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : X →L[R] Y :=
  ⟨⟨⟨f, hf.map_add'⟩, hf.map_smul'⟩, hf.cont⟩

@[simp]
theorem ContinuousLinearMap.mk'_eval
  (x : X) (f : X → Y) (hf : IsContinuousLinearMap R f) 
  : mk' R f hf x = f x := by rfl

macro "fun " x:ident " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun $x => $b) (by fprop))

macro "fun " x:ident " : " X:term " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by fprop))

macro "fun " "(" x:ident " : " X:term ")" " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by fprop))

@[app_unexpander ContinuousLinearMap.mk'] def unexpandContinuousLinearMapMk : Lean.PrettyPrinter.Unexpander

  | `($(_) $R $f:term $_:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' =>L[$R] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) =>L[$R] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun $x' : $ty =>L[$R] $b)
    | _  => throw ()
  | _  => throw ()


-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

namespace IsContinuousLinearMap

variable 
  {R : Type _} [Semiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
  {Z : Type _} [TopologicalSpace Z] [AddCommMonoid Z] [Module R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace (E i)] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
  

theorem by_morphism {f : X → Y} (g : X →L[R] Y) (h : ∀ x, f x = g x) 
  : IsContinuousLinearMap R f :=
by
  have h' : f = g := by funext x; apply h
  rw[h']
  constructor
  apply g.1.1.2
  apply g.1.2
  apply g.2


  
-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

open ContinuousLinearMap

theorem id_rule 
  : IsContinuousLinearMap R fun x : X => x 
:= 
  by_morphism (ContinuousLinearMap.id R X) (by simp)


theorem const_rule 
  : IsContinuousLinearMap R fun _ : X => (0 : Y) 
:= 
  by_morphism 0 (by simp)


theorem comp_rule 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : Y → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => f (g x) 
:= 
  by_morphism ((mk' R f hf).comp (mk' R g hg)) 
  (by simp[ContinuousLinearMap.comp])


theorem let_rule 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap R (fun (xy : X×Y) => f xy.1 xy.2))
  : IsContinuousLinearMap R fun x => let y := g x; f x y
:= 
  by_morphism ((mk' R (fun (xy : X×Y) => f xy.1 xy.2) hf).comp ((ContinuousLinearMap.id R X).prod (mk' R g hg))) 
  (by simp[ContinuousLinearMap.comp])


theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, IsContinuousLinearMap R (f i))
  : IsContinuousLinearMap R (fun x i => f i x) 
:=
  by_morphism (ContinuousLinearMap.pi fun i => (mk' R (fun x => f i x) (hf i)))
  (by simp)


theorem proj_rule (i : ι)
  : IsContinuousLinearMap R fun f : (i : ι) → E i => f i
:= 
  by_morphism (ContinuousLinearMap.proj i) (by simp)


--------------------------------------------------------------------------------
-- Register IsContinuousLinearMap ----------------------------------------------
--------------------------------------------------------------------------------

open Lean Meta SciLean FProp
def fpropExt : FPropExt where
  fpropName := ``IsContinuousLinearMap
  getFPropFun? e := 
    if e.isAppOf ``IsContinuousLinearMap then

      if let .some f := e.getArg? 10 then
        some f
      else 
        none
    else
      none

  replaceFPropFun e f := 
    if e.isAppOf ``IsContinuousLinearMap then
      e.modifyArg (fun _ => f) 10
    else          
      e

  identityRule    e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``IsContinuousLinearMap.id_rule 
      origin := .decl ``IsContinuousLinearMap.id_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  constantRule e := 
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``IsContinuousLinearMap.const_rule 
      origin := .decl ``IsContinuousLinearMap.const_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  compRule e f g := do
    let .some R := e.getArg? 0
      | return none

    let HF ← mkAppM ``IsContinuousLinearMap #[R, f]
    let .some hf ← FProp.fprop HF
      | trace[Meta.Tactic.fprop.discharge] "IsContinuousLinearMap.comp_rule, failed to discharge hypotheses {HF}"
        return none

    let HG ← mkAppM ``IsContinuousLinearMap #[R, g]
    let .some hg ← FProp.fprop HG
      | trace[Meta.Tactic.fprop.discharge] "IsContinuousLinearMap.comp_rule, failed to discharge hypotheses {HG}"
        return none

    mkAppM ``IsContinuousLinearMap.comp_rule #[g,hg,f,hf]

  lambdaLetRule e f g := do
    -- let thm : SimpTheorem :=
    -- {
    --   proof  := mkConst ``IsContinuousLinearMap.let_rule 
    --   origin := .decl ``IsContinuousLinearMap.let_rule 
    --   rfl    := false
    -- }
    -- FProp.tryTheorem? e thm (fun _ => pure none)
    let .some R := e.getArg? 0
      | return none

    let HF ← mkAppM ``IsContinuousLinearMap #[R, (← mkUncurryFun 2 f)]
    let .some hf ← FProp.fprop HF
      | trace[Meta.Tactic.fprop.discharge] "IsContinuousLinearMap.let_rule, failed to discharge hypotheses {HF}"
        return none

    let HG ← mkAppM ``IsContinuousLinearMap #[R, g]
    let .some hg ← FProp.fprop HG
      | trace[Meta.Tactic.fprop.discharge] "IsContinuousLinearMap.let_rule, failed to discharge hypotheses {HG}"
        return none

    mkAppM ``IsContinuousLinearMap.let_rule #[g,hg,f,hf]

  lambdaLambdaRule e _ :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``IsContinuousLinearMap.pi_rule 
      origin := .decl ``IsContinuousLinearMap.pi_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)

  projRule e :=
    let thm : SimpTheorem :=
    {
      proof  := mkConst ``IsContinuousLinearMap.proj_rule 
      origin := .decl ``IsContinuousLinearMap.proj_rule 
      rfl    := false
    }
    FProp.tryTheorem? e thm (fun _ => pure none)


  discharger _ := return none

-- register fderiv
#eval show Lean.CoreM Unit from do
  modifyEnv (λ env => FProp.fpropExt.addEntry env (``IsContinuousLinearMap, IsContinuousLinearMap.fpropExt))

end SciLean.IsContinuousLinearMap

--------------------------------------------------------------------------------

open SciLean IsContinuousLinearMap ContinuousLinearMap

variable
  {R : Type _} [Semiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
  {Z : Type _} [TopologicalSpace Z] [AddCommMonoid Z] [Module R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace (E i)] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]


-- FunLike.coe -----------------------------------------------------------------
--------------------------------------------------------------------------------


-- This one is necessary because of some issues with topology on product spaces
-- This problem has to be a bug somewhere ...
@[fprop]
theorem FunLike.coe.arg_a.IsContinuousLinearMap_rule
  (f : Y →L[R] Z) 
  : IsContinuousLinearMap R f := 
  by_morphism f (by simp)


@[fprop]
theorem FunLike.coe.arg_a.IsContinuousLinearMap_rule'
  (f : Y →L[R] Z) (g : X → Y) (hg : IsContinuousLinearMap R g) 
  : IsContinuousLinearMap R (fun x => f (g x)) := 
  by_morphism (f.comp (mk' R g hg)) (by simp)


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------


@[fprop]
theorem id.arg_a.IsContinuousLinearMap_rule
  : IsContinuousLinearMap R (id : X → X)
:= 
  by_morphism (ContinuousLinearMap.id R X) (by simp)



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.mk.arg_fstsnd.IsContinuousLinearMap_rule
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => (g x, f x)
:= 
  by_morphism ((mk' R g hg).prod (mk' R f hf)) 
  (by simp)



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.fst.arg_self.IsContinuousLinearMap_rule
  (f : X → Y×Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun (x : X) => (f x).fst
:= 
  by_morphism ((ContinuousLinearMap.fst R Y Z).comp (mk' R f hf))
  (by simp)



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fprop]
theorem Prod.snd.arg_self.IsContinuousLinearMap_rule
  (f : X → Y×Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun (x : X) => (f x).snd
:= 
  by_morphism ((ContinuousLinearMap.snd R Y Z).comp (mk' R f hf))
  (by simp)



-- Neg.neg ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem Neg.neg.arg_a0.IsContinuousLinearMap_rule 
  {R : Type _} [Ring R]
  {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [TopologicalAddGroup Y]
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => - f x
:= 
  by_morphism (ContinuousLinearMap.neg.neg (mk' R f hf))
  (by simp[ContinuousLinearMap.neg])



-- HAdd.hAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HAdd.hAdd.arg_a0a1.IsContinuousLinearMap_rule [ContinuousAdd Y]
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x + g x
:= 
  by_morphism (ContinuousLinearMap.add.add (mk' R f hf) (mk' R g hg))
  (by simp[ContinuousLinearMap.add])



-- HSub.hSub -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem HSub.hSub.arg_a0a1.IsContinuousLinearMap_rule 
  {R : Type _} [Ring R]
  {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [TopologicalAddGroup Y]
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x - g x
:= 
  by_morphism (ContinuousLinearMap.sub.sub (mk' R f hf) (mk' R g hg))
  (by simp[ContinuousLinearMap.sub])



-- HMul.hMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

def ContinuousLinearMap.mul_left 
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [Semiring X] [Algebra R X] [TopologicalSemiring X] 
  (x' : X) 
  : X →L[R] X := 
  ⟨⟨⟨fun x => x' * x, 
    by apply mul_add⟩, 
    by simp⟩, 
    by continuity⟩


def ContinuousLinearMap.mul_right 
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [Semiring X] [Algebra R X] [TopologicalSemiring X] 
  (x' : X) 
  : X →L[R] X := 
  ⟨⟨⟨fun x => x * x', 
    fun a b => add_mul a b x'⟩, 
    by simp⟩, 
    by continuity⟩


@[fprop]
theorem HMul.hMul.arg_a0.IsContinuousLinearMap_rule
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra R Y] [TopologicalSemiring Y] 
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  (y' : Y) 
  : IsContinuousLinearMap R fun x => f x * y'
:= 
  by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_right y') (mk' R f hf))
  (by simp[ContinuousLinearMap.mul_right])


@[fprop]
theorem HMul.hMul.arg_a1.IsContinuousLinearMap_rule
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra R Y] [TopologicalSemiring Y] 
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  (y' : Y) 
  : IsContinuousLinearMap R fun x => y' * f x
:= 
  by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_left y') (mk' R f hf))
  (by simp[ContinuousLinearMap.mul_left])



-- Smul.smul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

/-- Creates `fun x =>L[R] r • g x` -/
def ContinuousLinearMap.smulLeft 
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y] [ContinuousConstSMul R Y]
  (g : X →L[R] Y)
  (r : R) 
  : X →L[R] Y := 
  let f : Y →L[R] Y := 
    ⟨⟨⟨fun x => r • x, 
      DistribMulAction.smul_add r⟩, 
      smul_comm r⟩, 
      ContinuousConstSMul.continuous_const_smul r⟩
  f.comp g


@[simp]
def ContinuousLinearMap.smul_left 
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y] [ContinuousConstSMul R Y]
  (g : X →L[R] Y)
  (r : R) (x : X)
  : smulLeft g r x = r • g x := by rfl


@[fprop]
theorem HSMul.hSMul.arg_a0.IsContinuousLinearMap_rule
  [TopologicalSpace R] [ContinuousSMul R Y]
  (f : X → R) (hf : IsContinuousLinearMap R f)
  (y : Y) 
  : IsContinuousLinearMap R fun x => f x • y
:= 
  by_morphism (ContinuousLinearMap.smulRight (mk' R f hf) y)
  (by simp)


@[fprop]
theorem HSMul.hSMul.arg_a1.IsContinuousLinearMap_rule 
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y] [ContinuousConstSMul R Y]
  (c : R)
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => c • f x
:= 
  by_morphism (ContinuousLinearMap.smulLeft (mk' R f hf) c)
  (by simp)



-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

/-- Creates `fun x =>L[R] g x / y` -/
def ContinuousLinearMap.divRight
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  (g : X →L[R] K) (y : K) 
  : X →L[R] K := 
  let f : K →L[R] K := 
    ⟨⟨⟨fun x => x / y, 
      by apply fun a b => add_div a b y⟩, 
      by intro r x; simp; (repeat rw[div_eq_inv_mul]); apply mul_smul_comm⟩, 
      by continuity⟩
  f.comp g


@[simp]
def ContinuousLinearMap.div_right
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  (g : X →L[R] K) (y : K) (x : X)
  : divRight g y x = g x / y := by rfl


@[fprop]
theorem HDiv.hDiv.arg_a0.IsContinuousLinearMap_rule
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  (f : X → K) (hf : IsContinuousLinearMap R f) (y : K) 
  : IsContinuousLinearMap R fun x => f x / y
:= 
  by_morphism (ContinuousLinearMap.divRight (mk' R f hf) y)
  (by simp)


-- Finset.sum -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

open BigOperators in
@[fprop]
theorem Finset.sum.arg_f.IsContinuousLinearMap_rule
  (f : X → ι → Y) (_ : ∀ i, IsContinuousLinearMap R fun x : X => f x i) (A : Finset ι)
  : IsContinuousLinearMap R fun x => ∑ i in A, f x i := 
{
  map_add'  := sorry_proof
  map_smul' := sorry_proof
  cont := sorry_proof
}

-- do we need this one?
-- open BigOperators in
-- @[fprop]
-- theorem Finset.sum.arg_f.IsContinuousLinearMap_rule'
--   (f : ι → X → Y) (hf : ∀ i, IsContinuousLinearMap R (f i)) (A : Finset ι)
--   : IsContinuousLinearMap R fun (x : X) => ∑ i in A, f i x := sorry_proof


-- d/ite -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem ite.arg_te.IsContinuousLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsContinuousLinearMap R t) (he : IsContinuousLinearMap R e)
  : IsContinuousLinearMap R fun x => ite c (t x) (e x) := 
by
  induction dec
  case isTrue h  => simp[h]; fprop
  case isFalse h => simp[h]; fprop


@[fprop]
theorem dite.arg_te.IsContinuousLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsContinuousLinearMap R (t p)) 
  (e : ¬c → X → Y) (he : ∀ p, IsContinuousLinearMap R (e p))
  : IsContinuousLinearMap R fun x => dite c (t · x) (e · x) := 
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he


-------------------------------------------------------------------------------- 

section InnerProductSpace

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module K X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]


-- Inner -----------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[fprop]
theorem Inner.inner.arg_a0.IsContinuousLinearMap_rule
  (f : X → Y) (_ : IsContinuousLinearMap K f) (y : Y)
  : IsContinuousLinearMap K fun x => @inner K _ _ (f x) y :=
by
  sorry_proof

@[fprop]
theorem Inner.inner.arg_a1.IsContinuousLinearMap_rule
  (f : X → Y) (_ : IsContinuousLinearMap K f) (y : Y)
  : IsContinuousLinearMap K fun x => @inner K _ _ y (f x) :=
by
  sorry_proof


-- conj/starRingEnd ------------------------------------------------------------
-------------------------------------------------------------------------------- 
set_option linter.fpropDeclName false in
open ComplexConjugate in
@[fprop]
theorem starRingEnd.arg_a.IsContinuousLinearMap_rule
  (f : X → K) (_ : IsContinuousLinearMap K f)
  : IsContinuousLinearMap K fun x => conj (f x) :=
by
  sorry_proof


end InnerProductSpace
