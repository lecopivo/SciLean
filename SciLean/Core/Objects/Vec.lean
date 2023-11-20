import Mathlib.Algebra.Module.Basic
import Mathlib.Data.IsROrC.Lemmas
import Mathlib.Topology.Algebra.Module.LocallyConvex

import SciLean.Util.SorryProof

namespace SciLean


-- TODO: move this section
namespace Curve

variable {K : Type u} [NontriviallyNormedField K] 
variable {F : Type v} [AddCommGroup F] [Module K F] [TopologicalSpace F] -- [TopologicalAddGroup F] [ContinuousSMul K F]
variable {E : Type w} [AddCommGroup E] [Module K E] [TopologicalSpace E] -- [TopologicalAddGroup E] [ContinuousSMul K E]

open scoped Classical Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

def HasDerivAtFilter (f : K → F) (f' : F) (x : K) (L : Filter K) :=
  Tendsto (fun x' => (x' - x)⁻¹ • (f x' - f x)) L (nhds f')

def HasDerivAt (f : K → F) (f' : F) (x : K) :=
  HasDerivAtFilter f f' x (𝓝 x)

def DifferentiableAt (f : K → F) (x : K) :=
  ∃ f' : F, HasDerivAt f f' x

noncomputable
def deriv (f : K → F) (x : K) :=
  if h : ∃ f', HasDerivAt f f' x then Classical.choose h else 0

def Differentiable (f : K → F) :=
  ∀ x, DifferentiableAt f x

-- TODO: This should probably be true on small neighborhood of x not just *at* x
def DifferentiableAtN (f : K → F) (x : K) (n : Nat) :=
  match n with
  | 0 => ContinuousAt f x
  | n+1 => DifferentiableAt f x ∧ DifferentiableAtN (deriv f) x n

def DifferentiableN (f : K → F) (n : Nat) := ∀ x, DifferentiableAtN f x n
def SmoothAt        (f : K → F) (x : K)   := ∀ n, DifferentiableAtN f x n
def Smooth          (f : K → F)           := ∀ x n, DifferentiableAtN f x n

end Curve


-- __   __      _             ___
-- \ \ / /__ __| |_ ___ _ _  / __|_ __  __ _ __ ___
--  \ V / -_) _|  _/ _ \ '_| \__ \ '_ \/ _` / _/ -_)
--   \_/\___\__|\__\___/_|   |___/ .__/\__,_\__\___|
--                               |_|
-- At the and we will use Convenient Vector Space. It is a special kind of topological vector space
/-- Vectors space `X` over field `K`

More precisely this is Convenient Vector Space which is a special class of vector spaces
which allow very general definition of differentiability. In particular, the space `C∞(ℝ,ℝ)`, 
smooth functions on real numbers, is Convenient Vector Spaces but fails to be Banach space.
-/
class Vec (K : Type _) [IsROrC K] (X : Type _) 
  extends 
    AddCommGroup X,
    TopologicalSpace X,
    TopologicalAddGroup X,
    Module K X,
    ContinuousSMul K X
  where
    -- locally convex in some sense, mathlib definition is odd
    -- mild completeness condition
    scalar_wise_smooth : ∀ (c : K → X),
      Curve.Smooth c
      ↔ 
      ∀ x' : X →L[K] K, Curve.Smooth (x'∘c)

section CommonVectorSpaces

  variable {α β ι : Type u}
  variable {K : Type _} [IsROrC K]
  variable {U V} [Vec K U] [Vec K V]
  variable {E : ι → Type v}

  instance {X} [Vec K X] : Inhabited X := ⟨0⟩

  -- instance : MulAction ℝ ℝ := MulAction.mk sorry_proof sorry_proof
  -- instance : DistribMulAction ℝ ℝ := DistribMulAction.mk sorry_proof sorry_proof
  -- instance : Module ℝ ℝ := Module.mk sorry_proof sorry_proof
  -- instance : Vec ℝ := Vec.mk


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

  abbrev ContinuousAdd.mkSorryProofs {α} [Add α] [TopologicalSpace α] : ContinuousAdd α := ContinuousAdd.mk sorry_proof
  abbrev ContinuousNeg.mkSorryProofs {α} [Neg α] [TopologicalSpace α] : ContinuousNeg α := ContinuousNeg.mk sorry_proof
  abbrev TopologicalAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [TopologicalSpace α] := 
   @TopologicalAddGroup.mk α _ (AddGroup.mkSorryProofs) (ContinuousAdd.mkSorryProofs) (ContinuousNeg.mkSorryProofs)

  abbrev ContinuousSMul.mkSorryProofs {α} [SMul K α] [TopologicalSpace α] : ContinuousSMul K α := ContinuousSMul.mk sorry_proof

  abbrev Vec.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [SMul K α] [TopologicalSpace α] : Vec K α :=
    Vec.mk (toAddCommGroup := AddCommGroup.mkSorryProofs) (toModule := Module.mkSorryProofs (addcommgroup := AddCommGroup.mkSorryProofs)) (toTopologicalAddGroup := TopologicalAddGroup.mkSorryProofs) (toContinuousSMul := ContinuousSMul.mkSorryProofs) sorry_proof

  instance [IsROrC K] : Vec K K where
    scalar_wise_smooth := sorry_proof
    
  -- instance [inst : Vec K U] : Vec K (α → U) := 
  --   -- option 1:
  --   -- Vec.mkSorryProofs
  --   -- option 2:
  --   -- have : Module K U := inst.toModule
  --   -- Vec.mk
  --   -- option 3:
  --   by cases inst; apply Vec.mk (scalar_wise_smooth := sorry_proof)


  instance(priority:=low) (α : Type _) (X : α → Type _) [inst : ∀ a, Vec K (X a)] : Vec K ((a : α) → X a) := 
    --Vec.mkSorryProofs
    let _ : ∀ a, Module K (X a) := fun a => (inst a).toModule
    let _ : ∀ a, TopologicalSpace (X a) := fun a => (inst a).toTopologicalSpace
    let _ : ∀ a, TopologicalAddGroup (X a) := fun a => (inst a).toTopologicalAddGroup
    let _ : ∀ a, ContinuousSMul K (X a) := fun a => (inst a).toContinuousSMul
    Vec.mk (scalar_wise_smooth := sorry_proof)

  instance [instU : Vec K U] [instV : Vec K V] : Vec K (U × V) := 
    by cases instU; cases instV; apply Vec.mk (scalar_wise_smooth := sorry_proof)

  instance : Vec K Unit := Vec.mk (scalar_wise_smooth := sorry_proof)


  infix:30 "⊕" => Sum.elim  -- X⊕Y→Type

  instance instVecSum
    (X Y : Type) (TX : X → Type) (TY : Y → Type)  (xy : X⊕Y) 
    [∀ x, Vec K (TX x)] [∀ y, Vec K (TY y)]
    : Vec K ((TX⊕TY) xy) 
    :=
    match xy with
    | .inl _ => by dsimp; infer_instance
    | .inr _ => by dsimp; infer_instance


end CommonVectorSpaces



section VecProp

class VecProp (K : Type _) [IsROrC K] {X : Type _} [Vec K X] (P : X → Prop) : Prop where
  add : ∀ x y, P x → P y → P (x + y)
  neg : ∀ x, P x → P (- x)
  smul : ∀ (r : K) x, P x → P (r • x)
  zero : P 0


variable {K : Type _} [IsROrC K] {X : Type _} [Vec K X] {P : X → Prop} [inst : VecProp K P]

instance : Add {x : X // P x} := ⟨λ x y => ⟨x.1 + y.1, inst.add x.1 y.1 x.2 y.2⟩⟩
instance : Sub {x : X // P x} := ⟨λ x y => ⟨x.1 - y.1, by simp[sub_eq_add_neg]; apply inst.add; apply x.2; apply inst.neg; apply y.2⟩⟩
instance : Neg {x : X // P x} := ⟨λ x => ⟨- x.1, inst.neg x.1 x.2⟩⟩
instance : SMul K {x : X // P x} := ⟨λ r x => ⟨r • x.1, inst.smul r x.1 x.2⟩⟩

instance : Zero {x : X // P x} := ⟨⟨0, inst.zero⟩⟩

-- instance : Vec K {x : X // P x} := sorry_proof

end VecProp
