import SciLean.Analysis.Convenient.Curve

namespace SciLean


/-- Vectors space `X` over field `K`

More precisely this is Convenient Vector Space which is a special class of vector spaces
which allow very general definition of differentiability. In particular, the space `C∞(ℝ,ℝ)`,
smooth functions on real numbers, is Convenient Vector Spaces but fails to be Banach space.

TODO: This class should be split into `AddGroup X` and `ConvenientSpace K X` similar to
  `NormedSpace K X`. This would allow to concider real and complex structure over `X` at the same
  time.

  It is unclear how to do this without typing all of this each time when we want to introduce a new
  space `X`. There is no short way to introduce locally convex vector space.
  ```
  variable {X : Type} [RCLike K] [AddCommGroup X] [UniformSpace X] [UniformAddGroup X]
    [Module ℝ X] [Module K X] [IsScalarTower ℝ K X] [ContinuousSMul K X] [LocallyConvexSpace ℝ X]
    [ConvenientSpace K X]
  ```
-/
class Vec (K : Type _) [RCLike K] (X : Type _)
  extends
    AddCommGroup X,
    UniformSpace X,
    UniformAddGroup X,
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
  variable {K : Type _} [RCLike K]
  variable {U V} [Vec K U] [Vec K V]
  variable {E : ι → Type v}

  instance {X} [Vec K X] : Inhabited X := ⟨0⟩

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
  set_option linter.unusedVariables false in
  abbrev Module.mkSorryProofs {α β} [Semiring α] [addcommgroup : AddCommGroup β] [SMul α β] : Module α β :=
    Module.mk (toDistribMulAction := DistribMulAction.mkSorryProofs) sorry_proof sorry_proof

  abbrev ContinuousAdd.mkSorryProofs {α} [Add α] [TopologicalSpace α] : ContinuousAdd α := ContinuousAdd.mk sorry_proof
  abbrev ContinuousNeg.mkSorryProofs {α} [Neg α] [TopologicalSpace α] : ContinuousNeg α := ContinuousNeg.mk sorry_proof
  abbrev TopologicalAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [TopologicalSpace α] :=
   @TopologicalAddGroup.mk α _ (AddGroup.mkSorryProofs) (ContinuousAdd.mkSorryProofs) (ContinuousNeg.mkSorryProofs)
  abbrev UniformAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [UniformSpace α] :=
   @UniformAddGroup.mk α _ (AddGroup.mkSorryProofs) sorry_proof -- (ContinuousAdd.mkSorryProofs) (ContinuousNeg.mkSorryProofs)

  abbrev ContinuousSMul.mkSorryProofs {α} [SMul K α] [TopologicalSpace α] : ContinuousSMul K α := ContinuousSMul.mk sorry_proof

  abbrev Vec.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [SMul K α] [UniformSpace α] : Vec K α :=
    Vec.mk (toAddCommGroup := AddCommGroup.mkSorryProofs) (toModule := Module.mkSorryProofs (addcommgroup := AddCommGroup.mkSorryProofs)) (toUniformAddGroup := UniformAddGroup.mkSorryProofs) (toContinuousSMul := ContinuousSMul.mkSorryProofs) sorry_proof

  instance [RCLike K] : Vec K K where
    scalar_wise_smooth := sorry_proof

  instance(priority:=low) (α : Type _) (X : α → Type _) [inst : ∀ a, Vec K (X a)] : Vec K ((a : α) → X a) :=
    let _ : ∀ a, Module K (X a) := fun a => (inst a).toModule
    let _ : ∀ a, UniformSpace (X a) := fun a => (inst a).toUniformSpace
    let _ : ∀ a, UniformAddGroup (X a) := fun a => (inst a).toUniformAddGroup
    let _ : ∀ a, ContinuousSMul K (X a) := fun a => (inst a).toContinuousSMul
    Vec.mk (scalar_wise_smooth := sorry_proof)

  instance [instU : Vec K U] [instV : Vec K V] : Vec K (U × V) :=
    by cases instU; cases instV; apply Vec.mk (scalar_wise_smooth := sorry_proof)

  instance : Vec K Unit := Vec.mk (scalar_wise_smooth := sorry_proof)

  instance instVecSum
    (X Y : Type) (TX : X → Type) (TY : Y → Type)  (xy : X⊕Y)
    [∀ x, Vec K (TX x)] [∀ y, Vec K (TY y)]
    : Vec K ((Sum.elim TX TY) xy)
    :=
    match xy with
    | .inl _ => by dsimp; infer_instance
    | .inr _ => by dsimp; infer_instance


end CommonVectorSpaces



section VecProp

class VecProp (K : Type _) [RCLike K] {X : Type _} [Vec K X] (P : X → Prop) : Prop where
  add : ∀ x y, P x → P y → P (x + y)
  neg : ∀ x, P x → P (- x)
  smul : ∀ (r : K) x, P x → P (r • x)
  zero : P 0

variable {K : Type _} [RCLike K] {X : Type _} [Vec K X] {P : X → Prop} [inst : VecProp K P]

instance : Add {x : X // P x} := ⟨λ x y => ⟨x.1 + y.1, inst.add x.1 y.1 x.2 y.2⟩⟩
instance : Sub {x : X // P x} := ⟨λ x y => ⟨x.1 - y.1, by simp[sub_eq_add_neg]; apply inst.add; apply x.2; apply inst.neg; apply y.2⟩⟩
instance : Neg {x : X // P x} := ⟨λ x => ⟨- x.1, inst.neg x.1 x.2⟩⟩
instance : SMul K {x : X // P x} := ⟨λ r x => ⟨r • x.1, inst.smul r x.1 x.2⟩⟩

instance : Zero {x : X // P x} := ⟨⟨0, inst.zero⟩⟩

end VecProp
