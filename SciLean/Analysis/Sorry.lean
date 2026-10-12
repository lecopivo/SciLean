module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.RCLike.Basic

public import SciLean.Util.SorryProof

@[expose] public section


namespace SciLean


variable {α β ι : Type u}
variable {K : Type _} [RCLike K]
variable {E : ι → Type v}

-- instance {X} [Vec K X] : Inhabited X := ⟨0⟩

abbrev AddSemigroup.mkSorryProofs {α} [Add α] : AddSemigroup α where
  add_assoc := sorry_proof
abbrev AddMonoid.mkSorryProofs {α} [Add α] [Zero α] : AddMonoid α where
  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  nsmul := nsmulRec
  nsmul_zero := sorry_proof
  nsmul_succ := sorry_proof
abbrev SubNegMonoid.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : SubNegMonoid α where
  toAddMonoid := AddMonoid.mkSorryProofs
  sub_eq_add_neg := sorry_proof
  zsmul := zsmulRec
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
abbrev AddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : AddGroup α where
  toSubNegMonoid := SubNegMonoid.mkSorryProofs
  neg_add_cancel := sorry_proof
abbrev AddCommGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] : AddCommGroup α where
  toAddGroup := AddGroup.mkSorryProofs
  add_comm := sorry_proof

abbrev MulAction.mkSorryProofs {α β} [Monoid α] [SMul α β] : MulAction α β :=
  { mul_smul := sorry_proof, one_smul := sorry_proof }
abbrev DistribMulAction.mkSorryProofs {α β} [Monoid α] [AddMonoid β] [SMul α β] : DistribMulAction α β :=
  { (MulAction.mkSorryProofs (α:=α) (β:=β)) with smul_add := sorry_proof, smul_zero := sorry_proof }
set_option linter.unusedVariables false in
abbrev Module.mkSorryProofs {α β} [Semiring α] [addcommgroup : AddCommGroup β] [SMul α β] : Module α β :=
  { (DistribMulAction.mkSorryProofs (α:=α) (β:=β)) with add_smul := sorry_proof, zero_smul := sorry_proof }

abbrev ContinuousAdd.mkSorryProofs {α} [Add α] [TopologicalSpace α] : ContinuousAdd α := ContinuousAdd.mk sorry_proof
abbrev ContinuousNeg.mkSorryProofs {α} [Neg α] [TopologicalSpace α] : ContinuousNeg α := ContinuousNeg.mk sorry_proof
abbrev IsTopologicalAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [TopologicalSpace α] :
    @IsTopologicalAddGroup α _ AddGroup.mkSorryProofs :=
  let _ : AddGroup α := AddGroup.mkSorryProofs
  let _ : ContinuousAdd α := ContinuousAdd.mkSorryProofs
  let _ : ContinuousNeg α := ContinuousNeg.mkSorryProofs
  IsTopologicalAddGroup.mk
abbrev IsUniformAddGroup.mkSorryProofs {α} [Add α] [Sub α] [Neg α] [Zero α] [UniformSpace α] :
    @IsUniformAddGroup α _ AddGroup.mkSorryProofs :=
  let _ : AddGroup α := AddGroup.mkSorryProofs
  @IsUniformAddGroup.mk α _ _ sorry_proof

abbrev ContinuousSMul.mkSorryProofs {α} [SMul K α] [TopologicalSpace α] : ContinuousSMul K α := ContinuousSMul.mk sorry_proof
