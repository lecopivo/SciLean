import SciLean.Mathlib.Algebra.Module.Basic
import SciLean.Mathlib.Data.Prod
import SciLean.Mathlib.Data.Pi
import SciLean.Mathlib.Data.PUnit

import SciLean.Algebra.Real

namespace SciLean

-- This is an auxiliary class mainly used for deriving
class SMul (X : Type u) extends HMul ℝ X X

-- __   __      _             ___
-- \ \ / /__ __| |_ ___ _ _  / __|_ __  __ _ __ ___
--  \ V / -_) _|  _/ _ \ '_| \__ \ '_ \/ _` / _/ -_)
--   \_/\___\__|\__\___/_|   |___/ .__/\__,_\__\___|
--                               |_|
-- At the and we will use Convenient Vector Space. It is a special kind of topological vector space

class Vec (X : Type u) extends AddCommGroup X, Module ℝ X

section CommonVectorSpaces

  variable {α β ι : Type u}
  variable {U V} [Vec U] [Vec V]
  variable {E : ι → Type v}

  -- instance : HMul ℝ PUnit PUnit := ⟨λ x y => PUnit.unit⟩
  -- instance : Vec PUnit :=
  -- {
  --   npow_zero' := by done

  --   add_assoc := sorry,
  --   add_comm := sorry,
  --   add_zero := sorry,
  --   zero_add := sorry
  -- }

  -- example {X} [Field X] : AddCommGroup X := by infer_instance

  instance {X} [Vec X] : Inhabited X := ⟨0⟩

  set_option synthInstance.maxHeartbeats 5000
  instance : MulAction ℝ ℝ := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ ℝ := DistribMulAction.mk sorry sorry
  instance : Module ℝ ℝ := Module.mk sorry sorry
  instance : Vec ℝ := Vec.mk
  -- instance (priority := high) [Vec U] : HMul ℝ U U := by infer_instance

  -- instance {A} [AddCommGroup A] : AddCommGroup (α → A) := AddCommGroup.mk sorry
  instance {A} [AddSemigroup A] : AddSemigroup (α → A) := AddSemigroup.mk sorry
  instance {A} [AddMonoid A]    : AddMonoid (α → A)    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
  instance {A} [SubNegMonoid A] : SubNegMonoid (α → A) := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
  instance {A} [AddGroup A]     : AddGroup (α → A)     := AddGroup.mk sorry
  instance {A} [AddCommGroup A] : AddCommGroup (α → A) := AddCommGroup.mk sorry

  instance {α β} {γ : Type w} [Monoid α] [MulAction α β] : MulAction α (γ → β) := MulAction.mk sorry sorry
  instance {A M} [AddMonoid A] [Monoid M] [DistribMulAction M A] : DistribMulAction M (α → A) := DistribMulAction.mk sorry sorry
  instance {M R} [AddCommGroup M] [Semiring R] [Module R M] : Module R (α → M) := Module.mk sorry sorry

  set_option synthInstance.maxHeartbeats 5000
  instance [Vec U] : Vec (α → U) := Vec.mk
  set_option synthInstance.maxHeartbeats 500

  instance {A B} [AddSemigroup A] [AddSemigroup B] : AddSemigroup (A × B) := AddSemigroup.mk sorry
  instance {A B} [AddMonoid A] [AddMonoid B]       : AddMonoid (A × B)    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
  instance {A B} [SubNegMonoid A] [SubNegMonoid B] : SubNegMonoid (A × B) := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
  instance {A B} [AddGroup A] [AddGroup B]         : AddGroup (A × B)     := AddGroup.mk sorry
  instance {A B} [AddCommGroup A] [AddCommGroup B] : AddCommGroup (A × B) := AddCommGroup.mk sorry

  instance {α β β'} [Monoid α] [MulAction α β] [MulAction α β'] : MulAction α (β × β') := MulAction.mk sorry sorry
  instance {A B M} [AddMonoid B] [AddMonoid A] [Monoid M] [DistribMulAction M A]  [DistribMulAction M B] : DistribMulAction M (A × B) := DistribMulAction.mk sorry sorry
  instance {M N R} [AddCommGroup M] [AddCommGroup N] [Semiring R] [Module R M] [Module R N] : Module R (M × N) := Module.mk sorry sorry

  set_option synthInstance.maxHeartbeats 5000
  instance [Vec U] [Vec V] : Vec (U × V) := Vec.mk
  set_option synthInstance.maxHeartbeats 500


  instance : AddSemigroup Unit := AddSemigroup.mk sorry
  instance : AddMonoid Unit    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
  instance : SubNegMonoid Unit := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
  instance : AddGroup Unit     := AddGroup.mk sorry
  instance : AddCommGroup Unit := AddCommGroup.mk sorry

  instance {α} [Monoid α] : MulAction α Unit := MulAction.mk sorry sorry
  instance {M} [Monoid M] : DistribMulAction M Unit := DistribMulAction.mk sorry sorry
  instance {R} [Semiring R] : Module R Unit := Module.mk sorry sorry

  set_option synthInstance.maxHeartbeats 50000
  instance : Vec Unit := Vec.mk
  set_option synthInstance.maxHeartbeats 500


end CommonVectorSpaces


namespace VecSimps
variable {X} [Vec X]
@[simp] theorem one_smul (x : X) : (1 : ℝ) * x = x := sorry
@[simp] theorem zero_smul (x : X) : (0 : ℝ) * x = (0 : X) := sorry
@[simp] theorem smul_zero (r : ℝ) : r * (0 : X) = (0 : X) := sorry
@[simp] theorem neg_one_smul (x : X) : (-1 : ℝ) * x = -x := sorry

@[simp] theorem add_neg_sub (x y : X) : x + -y = x - y := sorry
@[simp] theorem neg_add_sub (x y : X) : -x + y = y - x := sorry

@[simp] theorem smul_smul_mul (r s: ℝ) (x : X) : r * (s * x) = ((r * s) * x) := sorry


@[simp] theorem add_same_1 (a b : ℝ) (x : X) : a*x + b*x = (a+b)*x := sorry
@[simp] theorem add_same_2 (a : ℝ) (x : X) : a*x + x = (a+1)*x := sorry
@[simp] theorem add_same_3 (a : ℝ) (x : X) : x + a*x = (1+a)*x := sorry
@[simp] theorem add_same_4 (x : X) : x + x = (2:ℝ)*x := sorry


end VecSimps



section VecProp

class VecProp {X : Type} [Vec X] (P : X → Prop) : Prop where
  add : ∀ x y, P x → P y → P (x + y)
  neg : ∀ x, P x → P (- x)
  smul : ∀ (r : ℝ) x, P x → P (r * x)
  zero : P 0

variable {X : Type} [Vec X] {P : X → Prop} [inst : VecProp P]

instance : Add {x : X // P x} := ⟨λ x y => ⟨x.1 + y.1, inst.add x.1 y.1 x.2 y.2⟩⟩
instance : Sub {x : X // P x} := ⟨λ x y => ⟨x.1 - y.1, sorry⟩⟩
instance : Neg {x : X // P x} := ⟨λ x => ⟨- x.1, inst.neg x.1 x.2⟩⟩
instance : HMul ℝ {x : X // P x} {x : X // P x} := ⟨λ r x => ⟨r * x.1, inst.smul r x.1 x.2⟩⟩

instance : Zero {x : X // P x} := ⟨⟨0, inst.zero⟩⟩

instance : AddSemigroup {x : X // P x} := AddSemigroup.mk sorry
instance : AddMonoid {x : X // P x}    := AddMonoid.mk sorry sorry nsmulRec sorry sorry
instance : SubNegMonoid {x : X // P x} := SubNegMonoid.mk sorry zsmulRec sorry sorry sorry
instance : AddGroup {x : X // P x}     := AddGroup.mk sorry
instance : AddCommGroup {x : X // P x} := AddCommGroup.mk sorry

instance : MulAction ℝ {x : X // P x} := MulAction.mk sorry sorry
instance : DistribMulAction ℝ {x : X // P x} := DistribMulAction.mk sorry sorry
instance : Module ℝ {x : X // P x} := Module.mk sorry sorry

-- This should get subset topology inherited from `X` 
-- Important: this topology is not the same as of `X ⟿ Y`
-- The question should Vec be ∞-complete? I'm not sure that it can be
instance : Vec {x : X // P x} := Vec.mk

end VecProp
