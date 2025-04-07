import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

import SciLean.Algebra.IsLinearMap

namespace SciLean

variable (R : Type _) [Semiring R]
    {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
    {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]


-- TODO: completely remove this is is the same as IsBoundedLinearMap
@[fun_prop]
structure IsContinuousLinearMap (f : X → Y) : Prop where
  linear : IsLinearMap R f
  cont : Continuous f


-- Lambda function notation ----------------------------------------------------
--------------------------------------------------------------------------------

def ContinuousLinearMap.mk'
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : X →L[R] Y :=
  ⟨⟨⟨f, hf.linear.map_add⟩, hf.linear.map_smul⟩, hf.cont⟩

@[simp, simp_core, simp_core ↓]
theorem ContinuousLinearMap.mk'_eval
  (x : X) (f : X → Y) (hf : IsContinuousLinearMap R f)
  : mk' R f hf x = f x := by rfl

@[simp, simp_core, simp_core ↓]
theorem ContinuousLinearMap.mk'_coe
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : mk' R f hf = f := by rfl

attribute [simp_core, simp_core↓]
  ContinuousLinearMap.add_apply
  ContinuousLinearMap.sub_apply
  ContinuousLinearMap.smul_apply


@[simp]
theorem ContinuousLinearMap.eta_reduce (f : X →L[R] Y)
  : (mk' R f ⟨⟨f.1.1.2,f.1.2⟩,f.2⟩) = f := by ext; simp

macro "fun " x:ident " =>L[" R:term "]'(" prf:term ")" b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun $x => $b) $prf)

macro "fun " x:ident " : " X:term " =>L[" R:term "]'(" prf:term ")" b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) $prf)

macro "fun " "(" x:ident " : " X:term ")" " =>L[" R:term "]'(" prf:term ")" b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) $prf)


macro "fun " x:ident " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun $x => $b) (by fun_prop))

macro "fun " x:ident " : " X:term " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by fun_prop))

macro "fun " "(" x:ident " : " X:term ")" " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by fun_prop))

@[app_unexpander ContinuousLinearMap.mk'] def unexpandContinuousLinearMapMk : Lean.PrettyPrinter.Unexpander

  | `($(_) $R $f:term $_:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' =>L[$R] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) =>L[$R] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun $x' : $ty =>L[$R] $b)
    | _  => `(fun x =>L[$R] $f x)
  | _  => throw ()


-- This theorem is necessary for `lsimp` tactic. Normal `simp` seems to have some fancy support
-- to perform congruence on functions like this automatically.
@[congr]
theorem ContinuousLinearMap.mk'_congr
    (f g : X → Y) (hf : IsContinuousLinearMap R f) (h : f = g) :
    (fun x =>L[R] f x) = ContinuousLinearMap.mk' R g (by rw[← h]; apply hf) := by ext; simp_all



-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

namespace IsContinuousLinearMap

set_option deprecated.oldSectionVars true

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
  constructor
  apply g.1.1.2
  apply g.1.2
  apply g.2


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

open ContinuousLinearMap IsContinuousLinearMap

@[fun_prop]
theorem id_rule : IsContinuousLinearMap R fun x : X => x :=
  by_morphism (ContinuousLinearMap.id R X) (by simp)

@[fun_prop]
theorem const_rule : IsContinuousLinearMap R fun _ : X => (0 : Y) :=
  by_morphism 0 (by simp)

@[fun_prop]
theorem comp_rule
    (g : X → Y) (hg : IsContinuousLinearMap R g)
    (f : Y → Z) (hf : IsContinuousLinearMap R f) :
    IsContinuousLinearMap R fun x => f (g x) :=
  by_morphism ((mk' R f hf).comp (mk' R g hg))
  (by simp[ContinuousLinearMap.comp])

@[fun_prop]
theorem apply_rule (i : ι) :
    IsContinuousLinearMap R fun f : (i : ι) → E i => f i :=
  by_morphism (ContinuousLinearMap.proj i) (by simp)

@[fun_prop]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, IsContinuousLinearMap R (f · i)) :
    IsContinuousLinearMap R (fun x i => f x i) :=
  by_morphism (ContinuousLinearMap.pi fun i => (mk' R (fun x => f x i) (hf i)))
  (by simp)

end IsContinuousLinearMap
end SciLean

--------------------------------------------------------------------------------

open SciLean IsContinuousLinearMap ContinuousLinearMap

set_option deprecated.oldSectionVars true

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
@[fun_prop]
theorem FunLike.coe.arg_a.IsContinuousLinearMap_rule (f : Y →L[R] Z) :
    IsContinuousLinearMap R (fun y => f y) :=
  by_morphism f (by simp)


@[fun_prop]
theorem FunLike.coe.arg_a.IsContinuousLinearMap_rule'
    (f : Y →L[R] Z) (g : X → Y) (hg : IsContinuousLinearMap R g) :
    IsContinuousLinearMap R (fun x => f (g x)) :=
  by_morphism (f.comp (mk' R g hg)) (by simp)


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.IsContinuousLinearMap_rule
    (g : X → Y) (hg : IsContinuousLinearMap R g)
    (f : X → Z) (hf : IsContinuousLinearMap R f) :
    IsContinuousLinearMap R fun x => (g x, f x) :=
  by_morphism ((mk' R g hg).prod (mk' R f hf))
  (by simp)


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.IsContinuousLinearMap_rule
    (f : X → Y×Z) (hf : IsContinuousLinearMap R f) :
    IsContinuousLinearMap R fun (x : X) => (f x).fst :=
  by_morphism ((ContinuousLinearMap.fst R Y Z).comp (mk' R f hf))
  (by simp)


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsContinuousLinearMap_rule
    (f : X → Y×Z) (hf : IsContinuousLinearMap R f) :
    IsContinuousLinearMap R fun (x : X) => (f x).snd :=
  by_morphism ((ContinuousLinearMap.snd R Y Z).comp (mk' R f hf))
  (by simp)


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.IsContinuousLinearMap_rule
    {R : Type _} [Ring R]
    {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module R X]
    {Y : Type _} [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [IsTopologicalAddGroup Y]
    (f : X → Y) (hf : IsContinuousLinearMap R f) :
    IsContinuousLinearMap R fun x => - f x
:=
  by_morphism (ContinuousLinearMap.neg.neg (mk' R f hf))
  (by simp[ContinuousLinearMap.neg])



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.IsContinuousLinearMap_rule [ContinuousAdd Y]
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x + g x
:=
  by_morphism (ContinuousLinearMap.add.add (mk' R f hf) (mk' R g hg))
  (by simp[ContinuousLinearMap.add])



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.IsContinuousLinearMap_rule
  {R : Type _} [Ring R]
  {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [IsTopologicalAddGroup Y]
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x - g x
:=
  by_morphism (ContinuousLinearMap.sub.sub (mk' R f hf) (mk' R g hg))
  (by simp[ContinuousLinearMap.sub])



-- HMul.hMul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

def ContinuousLinearMap.mul_left
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [Semiring X] [Algebra R X] [IsTopologicalSemiring X]
  (x' : X)
  : X →L[R] X :=
  ⟨⟨⟨fun x => x' * x,
    by apply mul_add⟩,
    by simp⟩,
    by continuity⟩


def ContinuousLinearMap.mul_right
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [Semiring X] [Algebra R X] [IsTopologicalSemiring X]
  (x' : X)
  : X →L[R] X :=
  ⟨⟨⟨fun x => x * x',
    fun a b => add_mul a b x'⟩,
    by simp⟩,
    by continuity⟩


@[fun_prop]
theorem HMul.hMul.arg_a0.IsContinuousLinearMap_rule
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y]
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  (y' : Y)
  : IsContinuousLinearMap R fun x => f x * y'
:=
  by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_right y') (mk' R f hf))
  (by simp[ContinuousLinearMap.mul_right])


@[fun_prop]
theorem HMul.hMul.arg_a1.IsContinuousLinearMap_rule
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y]
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


@[fun_prop]
theorem HSMul.hSMul.arg_a0.IsContinuousLinearMap_rule
  [TopologicalSpace R] [ContinuousSMul R Y]
  (f : X → R) (hf : IsContinuousLinearMap R f)
  (y : Y)
  : IsContinuousLinearMap R fun x => f x • y
:=
  by_morphism (ContinuousLinearMap.smulRight (mk' R f hf) y)
  (by simp)


@[fun_prop]
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


@[fun_prop]
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

@[fun_prop]
theorem Finset.sum.arg_f.IsContinuousLinearMap_rule
  (f : X → ι → Y) (_ : ∀ i, IsContinuousLinearMap R fun x : X => f x i) (A : Finset ι)
  : IsContinuousLinearMap R fun x => ∑ i ∈ A, f x i :=
{
  linear := sorry_proof
  cont := sorry_proof
}

-- @[fun_prop]
-- theorem SciLean.sum.arg_f.IsContinuousLinearMap_rule {ι} [IndexType ι]
--   (f : X → ι → Y) (_ : ∀ i, IsContinuousLinearMap R fun x : X => f x i)
--   : IsContinuousLinearMap R fun x => sum (f x) :=
-- {
--   linear := sorry_proof
--   cont := sorry_proof
-- }

@[fun_prop]
theorem SciLean.IndexType.sum.arg_f.IsContinuousLinearMap_rule {ι n} [IndexType ι n] [Fold ι]
  (f : X → ι → Y) (_ : ∀ i, IsContinuousLinearMap R fun x : X => f x i)
  : IsContinuousLinearMap R fun x => ∑ᴵ i, f x i :=
{
  linear := sorry_proof
  cont := sorry_proof
}

-- do we need this one?
-- open BigOperators in
-- @[fun_prop]
-- theorem Finset.sum.arg_f.IsContinuousLinearMap_rule'
--   (f : ι → X → Y) (hf : ∀ i, IsContinuousLinearMap R (f i)) (A : Finset ι)
--   : IsContinuousLinearMap R fun (x : X) => ∑ i in A, f i x := sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.IsContinuousLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsContinuousLinearMap R t) (he : IsContinuousLinearMap R e)
  : IsContinuousLinearMap R fun x => ite c (t x) (e x) :=
by
  induction dec
  case isTrue h  => simp[h]; fun_prop
  case isFalse h => simp[h]; fun_prop


@[fun_prop]
theorem dite.arg_te.IsContinuousLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsContinuousLinearMap R (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsContinuousLinearMap R (e p))
  : IsContinuousLinearMap R fun x => dite c (t · x) (e · x) :=
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he

@[fun_prop]
theorem SciLean.IsContinuousLinearMapMap.isLinearMap (f : X → Y) (hf : IsContinuousLinearMap R f) :
    IsLinearMap R f := hf.1

@[fun_prop]
theorem SciLean.IsContinuousLinearMap.continuous (f : X → Y) (hf : IsContinuousLinearMap R f) :
    Continuous f := hf.2

section NormedSpace

variable
  {K : Type _} [RCLike K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

--------------------------------------------------------------------------------
-- Differentiable --------------------------------------------------------------

set_option linter.unusedVariables false in
@[fun_prop]
theorem ContinuousLinearMap.mk'.arg_f.IsContinuousLinearMap
    (f : X → Y → Z) (hf : Continuous ↿f) (hfx : ∀ y, IsLinearMap K (f · y))
    (hfy : ∀ x, IsContinuousLinearMap K (f x ·)) :
    IsContinuousLinearMap K (fun x => fun y =>L[K] f x y) := by
  constructor
  · constructor
    · intro x x'; ext y; apply (hfx y).1 x x'
    · intro k x; ext y; apply (hfx y).2 k x
  · dsimp[autoParam]; sorry_proof

@[fun_prop]
theorem SciLean.IsContinuousLinearMap.differentiable (f : X → Y) (hf : IsContinuousLinearMap K f) :
    Differentiable K f := by
  have h : f = (fun x =>L[K] f x) := by rfl
  rw[h]
  fun_prop

@[fun_prop]
theorem SciLean.IsContinuousLinearMap.differentiableAt (x : X) (f : X → Y) (hf : IsContinuousLinearMap K f) :
    DifferentiableAt K f x := by
  have h : f = (fun x =>L[K] f x) := by rfl
  rw[h]
  fun_prop


end NormedSpace
