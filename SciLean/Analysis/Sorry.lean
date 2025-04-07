import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.RCLike.Basic

import SciLean.Util.SorryProof

namespace SciLean


variable {α β ι : Type u}
variable {K : Type _} [RCLike K]
variable {E : ι → Type v}

-- instance {X} [Vec K X] : Inhabited X := ⟨0⟩

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
abbrev IsTopologicalAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [TopologicalSpace α] :=
 @IsTopologicalAddGroup.mk α _ (AddGroup.mkSorryProofs) (ContinuousAdd.mkSorryProofs) (ContinuousNeg.mkSorryProofs)
abbrev IsUniformAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [UniformSpace α] :=
 @IsUniformAddGroup.mk α _ (AddGroup.mkSorryProofs) sorry_proof -- (ContinuousAdd.mkSorryProofs) (ContinuousNeg.mkSorryProofs)

abbrev ContinuousSMul.mkSorryProofs {α} [SMul K α] [TopologicalSpace α] : ContinuousSMul K α := ContinuousSMul.mk sorry_proof
