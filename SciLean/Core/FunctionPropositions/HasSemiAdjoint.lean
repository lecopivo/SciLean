import SciLean.Core.Objects.SemiInnerProductSpace
import SciLean.Core.FunctionPropositions.IsLinearMap
import SciLean.Core.Simp
import SciLean.Core.Meta.GenerateLinearMapSimp

import Mathlib.Tactic.FunTrans.Attr
import Mathlib.Tactic.FunTrans.Elab

set_option linter.unusedVariables false

open LeanColls

namespace SciLean

variable
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]

@[fun_prop]
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
@[fun_trans]
noncomputable
def semiAdjoint (f : X → Y) (y : Y) : X :=
  match Classical.dec (HasSemiAdjoint K f) with
  | isTrue h => Classical.choose h y
  | isFalse _ => 0

-- Basic identities ------------------------------------------------------------
--------------------------------------------------------------------------------

/-- `semiAdjoint K f ·` is always linear because either `f` has adjoint and is linear or
`semiAdjoint K f ·` is zero function and thus linear too. -/
@[fun_prop]
theorem semiAdjoint.arg_y.IsLinearMap_rule (f : X → Y) :
    IsLinearMap K (fun y => semiAdjoint K f y) := sorry_proof

#generate_linear_map_simps SciLean.semiAdjoint.arg_y.IsLinearMap_rule

def semi_inner_ext (x x' : X)
  : (∀ φ, TestFunction φ → ⟪x, φ⟫[K] = ⟪x', φ⟫[K])
    →
    x = x' := sorry_proof

def semiAdjoint_move (x : X) (y : Y) (hx : TestFunction x) (f : X → Y) (hf : HasSemiAdjoint K f) :
   ⟪semiAdjoint K f y, x⟫[K] = ⟪y, f x⟫[K] := sorry_proof

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

@[fun_prop]
theorem id_rule : HasSemiAdjoint K (fun x : X => x) := by
  apply Exists.intro (fun x => x) _
  simp

@[fun_prop]
theorem const_rule : HasSemiAdjoint K (fun _ : X => (0:Y)) := by
  apply Exists.intro (fun _ => 0) _
  simp; sorry_proof

@[fun_prop]
theorem comp_rule
    (f : Y → Z) (g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g) :
    HasSemiAdjoint K (fun x => f (g x)) := by
  apply Exists.intro (fun z => semiAdjoint K g (semiAdjoint K f z)) _
  intros; rw[semiAdjoint_move]; rw[semiAdjoint_move]
  sorry_proof -- HasSemiAdjoint should preserve test functions
  repeat assumption

@[fun_prop]
theorem apply_rule (i : ι) :
    HasSemiAdjoint K (fun x : (i : ι) → E i => x i) := by
  apply Exists.intro (fun (y : E i) j => if h : i=j then h▸y else 0) _
  intros; simp[Inner.inner]; sorry_proof

@[fun_prop]
theorem pi_rule
    (f : X → (i : ι) → E i) (hf : ∀ i, HasSemiAdjoint K (f · i)) :
    HasSemiAdjoint K (fun x i => f x i) := by
  -- apply Exists.intro (fun g => ∑ i, semiAdjoint K (f · i) (g i)) _
  sorry_proof


--------------------------------------------------------------------------------

open SciLean HasSemiAdjoint ContinuousLinearMap

variable
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {W : Type _} [SemiInnerProductSpace K W]
  {ι : Type _} [IndexType ι] [LawfulIndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.HasSemiAdjoint_rule
    (g : X → Y) (hg : HasSemiAdjoint K g)
    (f : X → Z) (hf : HasSemiAdjoint K f) :
    HasSemiAdjoint K fun x => (g x, f x) := by
  apply Exists.intro (fun yz => semiAdjoint K g yz.1 + semiAdjoint K f yz.2) _
  intros; dsimp[Inner.inner]
  rw[SemiInnerProductSpace.add_left]
  rw[semiAdjoint_move]; rw[semiAdjoint_move]
  repeat aesop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.HasSemiAdjoint_rule
    (f : X → Y×Z) (hf : HasSemiAdjoint K f) :
    HasSemiAdjoint K fun (x : X) => (f x).fst := by
  apply Exists.intro (fun y => semiAdjoint K f (y,0)) _
  intros; rw[semiAdjoint_move]; simp[Inner.inner]
  sorry_proof
  repeat assumption


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.HasSemiAdjoint_rule
    (f : X → Y×Z) (hf : HasSemiAdjoint K f) :
    HasSemiAdjoint K fun (x : X) => (f x).snd := by
  apply Exists.intro (fun z => semiAdjoint K f (0,z)) _
  intros; rw[semiAdjoint_move]; simp[Inner.inner]
  sorry_proof
  repeat assumption


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.HasSemiAdjoint_rule
    (f : X → Y) : HasSemiAdjoint K fun x => - f x := by
  have : HasSemiAdjoint K f := sorry_proof -- do a split on this
  apply Exists.intro (fun y => semiAdjoint K f (-y)) _
  intros; rw[semiAdjoint_move]; simp[Inner.inner]
  sorry_proof
  repeat assumption


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.HasSemiAdjoint_rule [ContinuousAdd Y]
    (f g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g) :
    HasSemiAdjoint K fun x => f x + g x := by sorry_proof


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.HasSemiAdjoint_rule
    (f g : X → Y) (hf : HasSemiAdjoint K f) (hg : HasSemiAdjoint K g) :
    HasSemiAdjoint K fun x => f x - g x := by
  sorry_proof


-- HMul.hMul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HMul.hMul.arg_a0.HasSemiAdjoint_rule
  (f : X → K) (y' : K) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => f x * y' :=
by sorry_proof

@[fun_prop]
theorem HMul.hMul.arg_a1.HasSemiAdjoint_rule
  (y' : K) (f : X → K) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => y' * f x :=
by sorry_proof


-- Smul.smul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSMul.hSMul.arg_a0.HasSemiAdjoint_rule
  {Y : Type _} [SemiHilbert K Y]
  (f : X → K) (y : Y) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => f x • y :=
by
  apply Exists.intro (fun (y' : Y) => ⟪y,y'⟫[K] • semiAdjoint K f 1) _
  sorry_proof

open ComplexConjugate in
@[fun_prop]
theorem HSMul.hSMul.arg_a1.HasSemiAdjoint_rule
  (c : K) (f : X → Y) (hf : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => c • f x :=
vby
  apply Exists.intro (fun (y' : Y) => conj c • semiAdjoint K f y') _
  sorry_proof



-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[fun_prop]
theorem HDiv.hDiv.arg_a0.HasSemiAdjoint_rule
  (f : X → K) (hf : HasSemiAdjoint K f) (y : K)
  : HasSemiAdjoint K fun x => f x / y :=
by
  apply Exists.intro (fun (y' : K) => (1/conj y) • semiAdjoint K f y') _
  sorry_proof


-- Finset.sum -------------------------------------------------------------------
--------------------------------------------------------------------------------

open BigOperators in
@[fun_prop]
theorem Finset.sum.arg_f.HasSemiAdjoint_rule {ι : Type _} [Fintype ι]
  (f : X → ι → Y) (_ : ∀ i, HasSemiAdjoint K fun x : X => f x i) (A : Finset ι)
  : HasSemiAdjoint K fun x => ∑ i in A, f x i :=
by
  unfold HasSemiAdjoint
  apply Exists.intro (fun (y' : Y) => ∑ i in A, semiAdjoint K (f · i) y' ) _
  sorry_proof

-- EnumType.sum -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem SciLean.IndexType.sum.arg_f.HasSemiAdjoint_rule
  (f : X → ι → Y) (hf : ∀ i, HasSemiAdjoint K fun x : X => f x i)
  : HasSemiAdjoint K fun x => ∑ i, f x i :=
by
  -- unfold HasSemiAdjoint
  -- apply Exists.intro (fun (y' : Y) => ∑ i, semiAdjoint K (f · i) y') _
  sorry_proof


-- do we need this one?
-- open BigOperators in
-- @[fun_prop]
-- theorem Finset.sum.arg_f.HasSemiAdjoint_rule'
--   (f : ι → X → Y) (hf : ∀ i, HasSemiAdjoint K (f i)) (A : Finset ι)
--   : HasSemiAdjoint K fun (x : X) => ∑ i in A, f i x := sorry_proof

-- conj/starRingEnd ------------------------------------------------------------
--------------------------------------------------------------------------------

open ComplexConjugate in
@[fun_prop]
theorem starRingEnd.arg_a.HasSemiAdjoint_rule
  (f : X → K) (_ : HasSemiAdjoint K f)
  : HasSemiAdjoint K fun x => conj (f x) :=
by
  sorry_proof


-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.HasSemiAdjoint_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : HasSemiAdjoint K t) (he : HasSemiAdjoint K e)
  : HasSemiAdjoint K fun x => ite c (t x) (e x) :=
by
  induction dec
  case isTrue h  => simp[h]; fun_prop
  case isFalse h => simp[h]; fun_prop


@[fun_prop]
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

@[fun_prop]
theorem Inner.inner.arg_a0.HasSemiAdjoint_rule
  (f : X → Y) (_ : HasSemiAdjoint K f) (y : Y)
  : HasSemiAdjoint K fun x => ⟪f x, y⟫[K] :=
by
  apply Exists.intro (fun (c : K) => (conj c) • semiAdjoint K f y) _
  sorry_proof

@[fun_prop]
theorem Inner.inner.arg_a1.HasSemiAdjoint_rule
  (f : X → Y) (_ : HasSemiAdjoint K f) (y : Y)
  : HasSemiAdjoint K fun x => ⟪y, f x⟫[K] :=
by
  apply Exists.intro (fun (c : K) => c • semiAdjoint K f y) _
  sorry_proof


end InnerProductSpace


-- semiAdjoint -----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem SciLean.semiAdjoint.arg_y.HasSemiAdjoint_rule
  (f : X → Y) (a0 : W → Y) (ha0 : HasSemiAdjoint K a0)
  : HasSemiAdjoint K (fun w => semiAdjoint K f (a0 w)) :=
by
  -- either `f` has semiadjoint then the total adjoint id `a0† f†`
  -- or `f` does not have semiadjoint and `f†` is zero thus map and that has adjoint
  sorry_proof
