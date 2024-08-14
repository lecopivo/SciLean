import SciLean.Algebra.IsLinearMap
import SciLean.Analysis.Convenient.CDifferentiable

set_option linter.unusedVariables false

namespace SciLean

set_option deprecated.oldSectionVars true

variable
  (K : Type _) [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]

@[fun_prop]
def IsSmoothLinearMap (f : X → Y) : Prop :=
  IsLinearMap K f ∧ CDifferentiable K f -- todo: probably change to `CContDiff K ∞ f`


--------------------------------------------------------------------------------

namespace IsSmoothLinearMap

@[fun_prop]
theorem isLinearMap {f : X → Y} (hf : IsSmoothLinearMap K f) : IsLinearMap K f := hf.1
@[fun_prop]
theorem cdifferentiable {f : X → Y} (hf : IsSmoothLinearMap K f) : CDifferentiable K f := hf.2

variable (X)
@[fun_prop]
theorem id_rule : IsSmoothLinearMap K (fun x : X => x) := by constructor <;> fun_prop

variable (Y)
@[fun_prop]
theorem const_zero_rule : IsSmoothLinearMap K (fun _ : X => (0 : Y)) := by
  constructor <;> first | fun_prop
variable {Y}

variable {X}

@[fun_prop]
theorem comp_rule
  (f : Y → Z) (g : X → Y)
  (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g)
  : IsSmoothLinearMap K (fun x => f (g x)) :=
by
  constructor <;> fun_prop

@[fun_prop]
theorem apply_rule (i : ι)
  : IsSmoothLinearMap K (fun (x : (i : ι) → E i) => x i)
  := by constructor <;> fun_prop

@[fun_prop]
theorem pi_rule
  (f : X → (i : ι) → E i) (hf : ∀ i, IsSmoothLinearMap K (f · i))
  : IsSmoothLinearMap K fun x i => f x i :=
by
  have := fun i => (hf i).1
  have := fun i => (hf i).2
  constructor
  · fun_prop
  · fun_prop


--------------------------------------------------------------------------------

open SciLean

variable
  {K : Type _} [RCLike K]
  {X : Type _} [Vec K X]
  {Y : Type _} [Vec K Y]
  {Z : Type _} [Vec K Z]
  {ι : Type _} [IndexType ι] [DecidableEq ι]
  {E : ι → Type _} [∀ i, Vec K (E i)]


-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.mk.arg_fstsnd.IsSmoothLinearMap_rule
    (f : X → Z) (g : X → Y)
    (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g) :
    IsSmoothLinearMap K fun x => (g x, f x) := by constructor <;> fun_prop


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.fst.arg_self.IsSmoothLinearMap_rule
    (f : X → Y×Z) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun (x : X) => (f x).fst := by
  constructor <;> fun_prop


-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Prod.snd.arg_self.IsSmoothLinearMap_rule
    (f : X → Y×Z) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun (x : X) => (f x).snd := by
  constructor <;> fun_prop


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Neg.neg.arg_a0.IsSmoothLinearMap_rule
    (f : X → Y) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun x => - f x := by
  constructor <;> fun_prop


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HAdd.hAdd.arg_a0a1.IsSmoothLinearMap_rule
    (f g : X → Y) (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g) :
    IsSmoothLinearMap K fun x => f x + g x := by
  constructor <;> fun_prop



-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSub.hSub.arg_a0a1.IsSmoothLinearMap_rule
    (f g : X → Y) (hf : IsSmoothLinearMap K f) (hg : IsSmoothLinearMap K g) :
    IsSmoothLinearMap K fun x => f x - g x := by
  constructor <;> fun_prop


-- -- HMul.hMul ---------------------------------------------------------------------
-- --------------------------------------------------------------------------------

-- todo: generalize to algebras
@[fun_prop]
theorem HMul.hMul.arg_a0.IsSmoothLinearMap_rule
    (f : X → K) (hf : IsSmoothLinearMap K f) (y' : K) :
    IsSmoothLinearMap K fun x => f x * y' := by
  constructor <;> fun_prop

-- todo: generalize to algebras
@[fun_prop]
theorem HMul.hMul.arg_a1.IsSmoothLinearMap_rule
    (f : X → K) (hf : IsSmoothLinearMap K f) (y' : K) :
    IsSmoothLinearMap K fun x => y' * f x  := by
  constructor <;> fun_prop


-- Smul.smul ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem HSMul.hSMul.arg_a0.IsSmoothLinearMap_rule
    (f : X → K) (y : Y) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun x => f x • y := by
  constructor <;> fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsSmoothLinearMap_rule
    (c : K) (f : X → Y) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun x => c • f x := by
  constructor <;> fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsSmoothLinearMap_rule_nat
    (c : ℕ) (f : X → Y) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun x => c • f x := by
  constructor <;> fun_prop

@[fun_prop]
theorem HSMul.hSMul.arg_a1.IsSmoothLinearMap_rule_int
    (c : ℤ) (f : X → Y) (hf : IsSmoothLinearMap K f) : IsSmoothLinearMap K fun x => c • f x := by
  constructor <;> fun_prop


-- IndexType.sum ----------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem IndexType.sum.arg_f.IsSmoothLinearMap_rule
    (f : X → ι → Y) (hf : ∀ i, IsSmoothLinearMap K (f · i)) :
    IsSmoothLinearMap K fun x => ∑ i, f x i := by constructor <;> fun_prop



-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.IsSmoothLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t e : X → Y) (ht : IsSmoothLinearMap K t) (he : IsSmoothLinearMap K e)
  : IsSmoothLinearMap K fun x => ite c (t x) (e x) :=
by
  induction dec
  case isTrue h  => simp[h]; fun_prop
  case isFalse h => simp[h]; fun_prop


@[fun_prop]
theorem dite.arg_te.IsSmoothLinearMap_rule
  (c : Prop) [dec : Decidable c]
  (t : c  → X → Y) (ht : ∀ p, IsSmoothLinearMap K (t p))
  (e : ¬c → X → Y) (he : ∀ p, IsSmoothLinearMap K (e p))
  : IsSmoothLinearMap K fun x => dite c (t · x) (e · x) :=
by
  induction dec
  case isTrue h  => simp[h]; apply ht
  case isFalse h => simp[h]; apply he

namespace SciLean
section OnFinVec

variable
  {K : Type _} [RCLike K]
  {IX : Type _} [IndexType IX] [DecidableEq IX] {X : Type _} [FinVec IX K X]
  {IY : Type _} [IndexType IY] [DecidableEq IY] {Y : Type _} [FinVec IY K Y]
  {IZ : Type _} [IndexType IZ] [DecidableEq IZ] {Z : Type _} [FinVec IZ K Z]

@[fun_prop]
theorem Basis.proj.arg_x.IsSmoothLinearMap_rule (i : IX)
  : IsSmoothLinearMap K (fun x : X => ℼ i x) := by constructor <;> fun_prop

@[fun_prop]
theorem DualBasis.dualProj.arg_x.IsSmoothLinearMap_rule (i : IX)
  : IsSmoothLinearMap K (fun x : X => ℼ' i x) := by constructor <;> fun_prop

@[fun_prop]
theorem BasisDuality.toDual.arg_x.IsSmoothLinearMap_rule
  : IsSmoothLinearMap K (fun x : X => BasisDuality.toDual x) := by constructor <;> fun_prop

@[fun_prop]
theorem BasisDuality.fromDual.arg_x.IsSmoothLinearMap_rule
  : IsSmoothLinearMap K (fun x : X => BasisDuality.fromDual x) := by constructor <;> fun_prop

end OnFinVec
end SciLean
