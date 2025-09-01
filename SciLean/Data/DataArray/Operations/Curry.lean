import SciLean.Data.DataArray.DataArray
import SciLean.Data.DataArray.Algebra

-- import SciLean.Data.VectorType.Base
-- import SciLean.Data.VectorType.BaseSimps
-- import SciLean.Data.VectorType.Optimize
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv

import SciLean.Meta.GenerateFunProp
import SciLean.Tactic.DataSynth.DefDataSynth
import SciLean.Tactic.ConvAssign
-- import SciLean.Analysis.AdjointSpace.HasAdjoint
-- import SciLean.Analysis.Calculus.HasRevFDeriv


namespace SciLean.DataArrayN

variable
  {X : Type u} [PlainDataType X]
  {I : Type v} {nI : ℕ} [IndexType I nI]
  {J : Type w} {nJ : ℕ} [IndexType J nJ]
  [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
  {K nK} [IndexType K nK]
  [HasRnEquiv X K R]


-- this macro is here only because `variable` can't add extra hypothesis to `def_fun_prop` command
-- maybe add a new command like `variable_fun_prop`
-- that wiil take those binders an elaborate them only one they are we introduce the context of the function
scoped macro "data_array_fun_prop" f:ident X:ident R:ident "in" xs:ident* ":" prop:term  "by" tac:tacticSeq : command =>
  `(def_fun_prop $f in $xs* {$R : Type*}
      [RealScalar $R] [PlainDataType $R] [BLAS (DataArray $R) $R $R]
      {K nK} [IndexType K nK] [HasRnEquiv $X K $R] :
      $prop by $tac)

-- this macro is here only because `variable` can't add extra hypothesis to `def_fun_prop` command
-- maybe add a new command like `variable_fun_prop`
-- that wiil take those binders an elaborate them only one they are we introduce the context of the function
scoped macro "data_array_data_synth_abbrev" f:ident X:ident R:ident "in" xs:ident*  bs:bracketedBinder* ":" prop:term  "by" tac:tacticSeq : command =>
  `(abbrev_data_synth $f in $xs* {$R : Type}  --- BUG in `abbrev_data_synth` it can't handle universe polymorphims here
      [RealScalar $R] [PlainDataType $R] [BLAS (DataArray $R) $R $R]
      {K nK} [IndexType K nK] [HasRnEquiv $X K $R] $bs* :
      $prop by $tac)


--- I want this to look this way
-- def_fun_prop_variable {R : Type*}
--   [RealScalar R] [PlainDataType R] [BLAS (DataArray R) R R]
--   {K nK} [IndexType K nK] [HasRnEquiv X K R]

-- def_fun_prop DataArrayN.curry in x : IsLinearMap R by sorry_proof
-- def_fun_prop DataArrayN.curry in x : Continuous by sorry_proof
-- ...



data_array_fun_prop curry X R in x : IsLinearMap R by sorry_proof
data_array_fun_prop curry X R in x : Continuous by sorry_proof
data_array_fun_prop curry X R in x : IsContinuousLinearMap R by constructor <;> fun_prop
data_array_fun_prop curry X R in x : Differentiable R by fun_prop


data_array_data_synth_abbrev curry X R in x (x₀) : (HasFDerivAt (𝕜:=R) · · x₀) by
  apply hasFDerivAt_from_isContinuousLinearMap
  fun_prop

data_array_data_synth_abbrev curry X R in x : HasFwdFDeriv R by
  apply hasFwdFDeriv_from_hasFDerivAt
  case deriv => intros; data_synth
  case simp => intros; simp; rfl

data_array_data_synth_abbrev curry X R in x : HasAdjoint R by
  conv => enter[3]; assign (fun x : X^[J]^[I] => x.uncurry)
  constructor
  case adjoint => intro x y; sorry_proof
  case is_linear => fun_prop

data_array_data_synth_abbrev curry X R in x : HasAdjointUpdate R by
  apply hasAdjointUpdate_from_hasAdjoint
  case adjoint => data_synth
  case simp => intros; rfl

data_array_data_synth_abbrev curry X R in x : HasRevFDeriv R by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl

data_array_data_synth_abbrev curry X R in x : HasRevFDerivUpdate R by
  apply hasRevFDerivUpdate_from_hasFDerivAt_hasAdjointUpdate
  case deriv => intros; data_synth
  case adjoint => intros; dsimp; data_synth
  case simp => rfl
