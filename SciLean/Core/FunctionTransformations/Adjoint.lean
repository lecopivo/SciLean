import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import SciLean.Mathlib.Analysis.InnerProductSpace.Prod

import SciLean.Core.FunctionPropositions.IsContinuousLinearMap

import SciLean.Notation

#exit -- right now `adjoint` can't work with `fun_trans` as it transforms bundles morphism

set_option linter.unusedVariables false

namespace ContinuousLinearMap.adjoint

variable
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- TODO: move to mathlib
instance {E : ι → Type _} [∀ i, UniformSpace (E i)] [∀ i, CompleteSpace (E i)] : CompleteSpace (PiLp 2 E) := by unfold PiLp; unfold WithLp; infer_instance


-- Set up custom notation for adjoint. Mathlib's notation for adjoint seems to be broken
instance (f : X →L[K] Y) : SciLean.Dagger f (ContinuousLinearMap.adjoint f : Y →L[K] X) := ⟨⟩


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

open SciLean

variable (X) (K)
theorem id_rule
  : (fun (x : X) =>L[K] x)† = fun x =>L[K] x :=
by
  have h : (fun (x : X) =>L[K] x) = ContinuousLinearMap.id K X := by rfl
  rw[h]; simp


variable (Y)
theorem const_rule
  : (fun (x : X) =>L[K] (0 : Y))† = fun x =>L[K] 0 :=
by
  sorry_proof
variable {Y}

theorem proj_rule [DecidableEq ι]
   (i : ι)
  : (fun (f : PiLp 2 (fun _ => X)) =>L[K] f i)†
    =
    fun x =>L[K] (fun j => if i=j then x else (0 : X))
  := sorry_proof
variable {X}


theorem prod_rule
  (f : X → Y) (g : X → Z)
  (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : ((fun x =>L[K] (f x, g x)) : X →L[K] Y×₂Z)†
    =
    fun yz : Y×₂Z =>L[K]
      let x₁ := (fun x =>L[K] f x)† yz.1
      let x₂ := (fun x =>L[K] g x)† yz.2
      x₁ + x₂ :=
by
  sorry_proof


theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] f (g x))†
    =
    fun z =>L[K]
      let y := (fun y =>L[K] f y)† z
      let x := (fun x =>L[K] g x)† y
      x :=
by
  have h : (fun x =>L[K] f (g x))
           =
           (fun y =>L[K] f y).comp (fun x =>L[K] g x)
         := by rfl
  rw[h]
  rw[ContinuousLinearMap.adjoint_comp]
  ext dx; simp


theorem let_rule
  (f : X → Y → Z) (g : X → Y)
  (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] let y := g x; f x y)†
    =
    fun z =>L[K]
      let xy := ((fun xy : X×₂Y =>L[K] f xy.1 xy.2)†) z
      let x' := ((fun x =>L[K] g x)†) xy.2
      xy.1 + x' :=
by
  have h : (fun x =>L[K] let y := g x; f x y)
           =
           (fun xy : X×₂Y =>L[K] f xy.1 xy.2).comp (fun x =>L[K] (x, g x))
         := by rfl
  rw[h, ContinuousLinearMap.adjoint_comp]
  have h' : ((fun x =>L[K] (x, g x)) : X →L[K] X×₂Y)†
            =
            (fun (xy : X×₂Y) =>L[K] xy.1 + (fun x =>L[K] g x)† xy.2)
          := by rw[prod_rule K (fun x => x) g (by fprop) hg]; simp[id_rule]
  rw[h']; rfl


open BigOperators in
theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsContinuousLinearMap K (f · i))
  : ((fun (x : X) =>L[K] fun (i : ι) => f x i) : X →L[K] PiLp 2 E)†
    =
    (fun x' =>L[K] ∑ i, (fun x =>L[K] f x i)† (x' i))
  := sorry_proof



--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------

variable
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]

open SciLean


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.adjoint_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : ((fun x =>L[K] (g x, f x)) : X →L[K] Y×₂Z)†
    =
    fun yz =>L[K]
      let x₁ := (fun x =>L[K] g x)† yz.1
      let x₂ := (fun x =>L[K] f x)† yz.2
      x₁ + x₂ :=
by sorry_proof


@[fprop]
theorem SciLean.ProdL2.mk.arg_fstsnd.IsContinuousLinearMap_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : IsContinuousLinearMap K (fun x => ProdL2.mk (g x) (f x)) :=
by
  unfold ProdL2.mk; fprop


@[ftrans]
theorem SciLean.ProdL2.mk.arg_fstsnd.adjoint_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] ProdL2.mk (g x) (f x))†
    =
    fun yz =>L[K]
      let x₁ := (fun x =>L[K] g x)† yz.1
      let x₂ := (fun x =>L[K] f x)† yz.2
      x₁ + x₂ :=
by
  unfold ProdL2.mk; ftrans



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.adjoint_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x =>L[K] (f x).1)†
    =
    (fun y =>L[K] ((fun x =>L[K] f x) : X →L[K] Y×₂Z)† (y,(0:Z))) :=
by
  sorry_proof


@[fprop]
theorem SciLean.ProdL2.fst.arg_self.IsContinuousLinearMap_rule
  (f : X → Y×₂Z) (hf : SciLean.IsContinuousLinearMap K f)
  : IsContinuousLinearMap K (fun x => ProdL2.fst (f x)) :=
by
  unfold ProdL2.fst; fprop


@[ftrans]
theorem SciLean.ProdL2.fst.arg_self.adjoint_rule
  (f : X → Y×₂Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x =>L[K] ProdL2.fst (f x))†
    =
    (fun y =>L[K] ((fun x =>L[K] f x) : X →L[K] Y×₂Z)† (y,(0:Z))) :=
by
  unfold ProdL2.fst; ftrans



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.adjoint_rule
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x =>L[K] (f x).2)†
    =
    (fun z =>L[K] ((fun x =>L[K] f x) : X →L[K] Y×₂Z)† ((0 :Y),z)) :=
by
  sorry_proof


@[fprop]
theorem SciLean.ProdL2.snd.arg_self.IsContinuousLinearMap_rule
  (f : X → Y×₂Z) (hf : SciLean.IsContinuousLinearMap K f)
  : IsContinuousLinearMap K (fun x => ProdL2.snd (f x)) :=
by
  unfold ProdL2.snd; fprop


@[ftrans]
theorem SciLean.ProdL2.snd.arg_self.adjoint_rule
  (f : X → Y×₂Z) (hf : SciLean.IsContinuousLinearMap K f)
  : (fun x =>L[K] ProdL2.snd (f x))†
    =
    (fun z =>L[K] ((fun x =>L[K] f x) : X →L[K] Y×₂Z)† ((0:Y),z)) :=
by
  unfold ProdL2.snd; ftrans



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.adjoint_rule
  (f g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] f x + g x)†
    =
    fun y =>L[K]
      let x₁ := (fun x =>L[K] f x)† y
      let x₂ := (fun x =>L[K] g x)† y
      x₁ + x₂ :=
by
  sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.adjoint_rule
  (f g : X → Y) (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] f x - g x)†
    =
    fun y =>L[K]
      let x₁ := (fun x =>L[K] f x)† y
      let x₂ := (fun x =>L[K] g x)† y
      x₁ - x₂ :=
by
  sorry_proof


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] - f x)†
    =
    fun y =>L[K] - (fun x =>L[K] f x)† y :=
by
  sorry_proof


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HMul.hMul.arg_a0.adjoint_rule
  (c : K) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] f x * c)†
    =
    fun y =>L[K] conj c • (fun x =>L[K] f x)† y :=
by
  sorry_proof

open ComplexConjugate in
@[ftrans]
theorem HMul.hMul.arg_a1.adjoint_rule
  (c : K) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] c * f x)†
    =
    fun y =>L[K] conj c • (fun x =>L[K] f x)† y :=
by
  rw[show (fun x =>L[K] c * f x) = (fun x =>L[K] f x * c) by ext x; simp[mul_comm]]
  apply HMul.hMul.arg_a0.adjoint_rule


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HSMul.hSMul.arg_a0.adjoint_rule
  (x' : X) (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] f x • x')†
    =
    fun y =>L[K] @inner K _ _ x' y • (fun x =>L[K] f x)† 1 :=
by
  sorry_proof

open ComplexConjugate in
@[ftrans]
theorem HSMul.hSMul.arg_a1.adjoint_rule
  (c : K) (g : X → Y) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] c • g x)†
    =
    fun y =>L[K] (conj c) • (fun x =>L[K] g x)† y :=
by
  sorry_proof


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem HDiv.hDiv.arg_a0.adjoint_rule
  (f : X → K) (c : K)
  (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] f x / c)†
    =
    fun y =>L[K] (conj c)⁻¹ • (fun x =>L[K] f x)† y :=
by
  sorry_proof


-- Finset.sum ------------------------------------------------------------------
--------------------------------------------------------------------------------

open BigOperators in
@[ftrans]
theorem Finset.sum.arg_f.adjoint_rule
  (f : X → ι → Y) (hf : ∀ i, IsContinuousLinearMap K (f · i))
  : (fun x =>L[K] ∑ i, f x i)†
    =
    (fun y =>L[K] ∑ i, (fun x =>L[K] f x i)† y) :=
by
  sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem ite.arg_te.adjoint_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsContinuousLinearMap K t) (he : IsContinuousLinearMap K e)
  : (fun x =>L[K] ite c (t x) (e x))†
    =
    fun y =>L[K]
      ite c ((fun x =>L[K] t x)† y) ((fun x =>L[K] e x)† y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]

@[ftrans]
theorem dite.arg_te.adjoint_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsContinuousLinearMap K (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsContinuousLinearMap K (e p))
  : (fun x =>L[K] dite c (t · x) (e · x))†
    =
    fun y =>L[K]
      dite c (fun p => (fun x =>L[K] t p x)† y)
             (fun p => (fun x =>L[K] e p x)† y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


-- Inner -----------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[ftrans]
theorem Inner.inner.arg_a0.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f) (y : Y)
  : (fun x =>L[K] @inner K _ _ (f x) y)†
    =
    fun z =>L[K] (conj z) • (fun x =>L[K] f x)† y :=
by
  sorry_proof

@[ftrans]
theorem Inner.inner.arg_a1.adjoint_rule
  (f : X → Y) (hf : IsContinuousLinearMap K f) (y : Y)
  : (fun x =>L[K] @inner K _ _ y (f x))†
    =
    fun z =>L[K] z • (fun x =>L[K] f x)† y :=
by
  sorry_proof


-- conj/starRingEnd ------------------------------------------------------------
--------------------------------------------------------------------------------
set_option linter.ftransDeclName false in
open ComplexConjugate in
@[ftrans]
theorem starRingEnd.arg_a0.adjoint_rule
  (f : X → K) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] conj (f x))†
    =
    fun z =>L[K] (fun x =>L[K] f x)† z :=
by
  sorry_proof
