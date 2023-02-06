import SciLean.Mathlib.Algebra.Module.Basic
import SciLean.Mathlib.Data.Prod
import SciLean.Mathlib.Data.Pi
import SciLean.Mathlib.Data.PUnit

import SciLean.Core.Real

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

  instance {X} [Vec X] : Inhabited X := ⟨0⟩

  instance : MulAction ℝ ℝ := MulAction.mk sorry sorry
  instance : DistribMulAction ℝ ℝ := DistribMulAction.mk sorry sorry
  instance : Module ℝ ℝ := Module.mk sorry sorry
  instance : Vec ℝ := Vec.mk


  def AddSemigroup.mkSorryProofs {α} [Add α] : AddSemigroup α := AddSemigroup.mk sorry_proof
  def AddMonoid.mkSorryProofs {α} [Add α] [Zero α] : AddMonoid α := 
    AddMonoid.mk (toAddSemigroup := AddSemigroup.mkSorryProofs) sorry_proof sorry_proof nsmulRec sorry_proof sorry_proof
  def SubNegMonoid.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α]  : SubNegMonoid α := 
    SubNegMonoid.mk (toAddMonoid := AddMonoid.mkSorryProofs) sorry_proof zsmulRec sorry_proof sorry_proof sorry_proof
  def AddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : AddGroup α :=
    AddGroup.mk (toSubNegMonoid := SubNegMonoid.mkSorryProofs) sorry_proof
  def AddCommGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : AddCommGroup α :=
    AddCommGroup.mk (toAddGroup := AddGroup.mkSorryProofs) sorry_proof

  def MulAction.mkSorryProofs {α β} [Monoid α] [HMul α β β] : MulAction α β := MulAction.mk sorry_proof sorry_proof
  def DistribMulAction.mkSorryProofs {α β} [Monoid α] [AddMonoid β] [HMul α β β] : DistribMulAction α β := 
    DistribMulAction.mk (toMulAction := MulAction.mkSorryProofs) sorry_proof sorry_proof
  def Module.mkSorryProofs {α β} [Semiring α] [addcommgroup : AddCommGroup β] [HMul α β β] : Module α β := 
    Module.mk (toDistribMulAction := DistribMulAction.mkSorryProofs) sorry_proof sorry_proof

  def Vec.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [HMul ℝ α α] : Vec α :=
    Vec.mk (toAddCommGroup := AddCommGroup.mkSorryProofs) (toModule := Module.mkSorryProofs (addcommgroup := AddCommGroup.mkSorryProofs))
    
  instance [Vec U] : Vec (α → U) := Vec.mkSorryProofs
  instance(priority:=low) (α : Type) (X : α → Type) [∀ a, Vec (X a)] : Vec ((a : α) → X a) := Vec.mkSorryProofs
  instance [Vec U] [Vec V] : Vec (U × V) := Vec.mkSorryProofs
  instance : Vec Unit := Vec.mkSorryProofs

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

-- This should get subset topology inherited from `X` 
-- Important: topology on `X→Y` is not the same as of `X ⟿ Y`
-- The question should Vec be ∞-complete? I'm not sure that it can be
instance : Vec {x : X // P x} := Vec.mkSorryProofs

end VecProp
