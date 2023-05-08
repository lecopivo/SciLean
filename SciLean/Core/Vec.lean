-- import SciLean.Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Basic
import SciLean.Mathlib.Data.Prod
import SciLean.Mathlib.Data.Pi
import SciLean.Mathlib.Data.PUnit

import SciLean.Core.Real

namespace SciLean


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


  abbrev AddSemigroup.mkSorryProofs {α} [Add α] : AddSemigroup α := AddSemigroup.mk sorry_proof
  abbrev AddMonoid.mkSorryProofs {α} [Add α] [Zero α] : AddMonoid α := 
    AddMonoid.mk (toAddSemigroup := AddSemigroup.mkSorryProofs) sorry_proof sorry_proof nsmulRec sorry_proof sorry_proof
  abbrev SubNegMonoid.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α]  : SubNegMonoid α := 
    SubNegMonoid.mk (toAddMonoid := AddMonoid.mkSorryProofs) sorry_proof zsmulRec sorry_proof sorry_proof sorry_proof
  abbrev AddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : AddGroup α :=
    AddGroup.mk (toSubNegMonoid := SubNegMonoid.mkSorryProofs) sorry_proof
  abbrev AddCommGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : AddCommGroup α :=
    AddCommGroup.mk (toAddGroup := AddGroup.mkSorryProofs) sorry_proof

  abbrev MulAction.mkSorryProofs {α β} [Monoid α] [SMul α β] : MulAction α β := MulAction.mk sorry_proof sorry_proof
  abbrev DistribMulAction.mkSorryProofs {α β} [Monoid α] [AddMonoid β] [SMul α β] : DistribMulAction α β := 
    DistribMulAction.mk (toMulAction := MulAction.mkSorryProofs) sorry_proof sorry_proof
  abbrev Module.mkSorryProofs {α β} [Semiring α] [addcommgroup : AddCommGroup β] [SMul α β] : Module α β := 
    Module.mk (toDistribMulAction := DistribMulAction.mkSorryProofs) sorry_proof sorry_proof

  abbrev Vec.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [SMul ℝ α] : Vec α :=
    Vec.mk (toAddCommGroup := AddCommGroup.mkSorryProofs) (toModule := Module.mkSorryProofs (addcommgroup := AddCommGroup.mkSorryProofs))
    
  instance [Vec U] : Vec (α → U) := Vec.mkSorryProofs
  instance(priority:=low) (α : Type) (X : α → Type) [∀ a, Vec (X a)] : Vec ((a : α) → X a) := Vec.mkSorryProofs
  instance [Vec U] [Vec V] : Vec (U × V) := Vec.mkSorryProofs
  instance : Vec Unit := Vec.mkSorryProofs


  infix:30 "⊕" => Sum.elim  -- X⊕Y→Type

  instance instVecSum
    (X Y : Type) (TX : X → Type) (TY : Y → Type)  (xy : X⊕Y) 
    [∀ x, Vec (TX x)] [∀ y, Vec (TY y)]
    : Vec ((TX⊕TY) xy) 
    :=
    match xy with
    | .inl _ => by dsimp; infer_instance
    | .inr _ => by dsimp; infer_instance


end CommonVectorSpaces



section VecProp

class VecProp {X : Type} [Vec X] (P : X → Prop) : Prop where
  add : ∀ x y, P x → P y → P (x + y)
  neg : ∀ x, P x → P (- x)
  smul : ∀ (r : ℝ) x, P x → P (r • x)
  zero : P 0

variable {X : Type} [Vec X] {P : X → Prop} [inst : VecProp P]

instance : Add {x : X // P x} := ⟨λ x y => ⟨x.1 + y.1, inst.add x.1 y.1 x.2 y.2⟩⟩
instance : Sub {x : X // P x} := ⟨λ x y => ⟨x.1 - y.1, sorry⟩⟩
instance : Neg {x : X // P x} := ⟨λ x => ⟨- x.1, inst.neg x.1 x.2⟩⟩
instance : SMul ℝ {x : X // P x} := ⟨λ r x => ⟨r • x.1, inst.smul r x.1 x.2⟩⟩

instance : Zero {x : X // P x} := ⟨⟨0, inst.zero⟩⟩

-- This should get subset topology inherited from `X` 
-- Important: topology on `X→Y` is not the same as of `X ⟿ Y`
-- The question should Vec be ∞-complete? I'm not sure that it can be
instance : Vec {x : X // P x} := Vec.mkSorryProofs

end VecProp
