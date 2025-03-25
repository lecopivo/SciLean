import SciLean.Algebra.MatrixType.Basic
import SciLean.Analysis.Calculus.HasRevFDeriv
import SciLean.Analysis.Calculus.HasFwdFDeriv
import SciLean.Tactic.DataSynth.DefDataSynth
import SciLean.Analysis.Calculus.ContDiff

namespace SciLean

variable
  {M : Type*} [MatrixMulNotation M]
  {R : Type*} {_ : RCLike R}
  {X : Type*} {_ : NormedAddCommGroup X} {_ : AdjointSpace R X}
  {Y : Type*} {_ : NormedAddCommGroup Y} {_ : AdjointSpace R Y}
  {W : Type*} [NormedAddCommGroup W] [AdjointSpace R W]
  [NormedAddCommGroup M] [AdjointSpace R M] [MatrixType R Y X M]

set_default_scalar R

@[fun_prop]
theorem vecMatMul.arg_A.IsContinuousLinearMap_rule (A : M) :
  IsContinuousLinearMap R (fun y : Y => y * A) := sorry_proof

@[fun_prop]
theorem vecMatMul.arg_x.IsContinuousLinearMap_rule (y : Y) :
  IsContinuousLinearMap R (fun A : M => y * A) := sorry_proof

@[fun_prop]
theorem vecMatMul.arg_yA.ContDiff_rule :
  ContDiff R ⊤ (fun yA : Y×M => yA.1 * yA.2) := sorry_proof

-- todo: generate automatically
@[fun_prop]
theorem vecMatMul.arg_yA.Differentiable_rule :
  Differentiable R (fun yA : Y×M => yA.1 * yA.2) := by fun_prop

-- todo: generate automatically
@[fun_prop]
theorem vecMatMul.arg_yA.Continusous_rule :
  Continuous (fun yA : Y×M => yA.1 * yA.2) := by fun_prop



@[data_synth]
theorem vecMatMul.arg_yA.HasFwdFDeriv_rule :
  HasFwdFDeriv R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA dyA =>
      let' (y,A) := yA
      let' (dy,dA) := dyA
      (y*A, vecMatMulAdd (1:R) y dA (1:R) (dy*A))) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_A.HasFwdFDeriv_rule (y : Y) :
  HasFwdFDeriv R
    (fun A : M => y * A)
    (fun A dA =>
      (y*A, y*dA)) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_x.HasFwdFDeriv_rule (A : M) :
  HasFwdFDeriv R
    (fun y : Y => y * A)
    (fun y dy =>
      (y*A, dy*A)) := sorry_proof


@[data_synth]
theorem vecMatMul.arg_y.HasAdjoint_rule (A : M) :
  HasAdjoint R
    (fun y : Y => y * A)
    (fun x => A * x) := sorry_proof

@[data_synth]
theorem vecMatMul.arg_y.HasAdjointUpdate_rule (A : M) :
  HasAdjointUpdate R
    (fun y : Y => y * A)
    (fun x y' => matVecMulAdd (1:R) A x (1:R) y') := sorry_proof

@[data_synth]
theorem vecMatMul.arg_A.HasAdjoint_rule (y : Y) :
  HasAdjoint R
    (fun A : M => y * A)
    (fun x => y ⊗ x) := sorry_proof

@[data_synth]
theorem vecMatMul.arg_A.HasAdjointUpdate_rule (y : Y) :
  HasAdjointUpdate R
    (fun A : M => y * A)
    (fun x A' => tmulAdd (1:R) y x A') := sorry_proof


@[data_synth]
theorem vecMatMul.arg_yA.HasRevFDeriv_rule :
  HasRevFDeriv R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA =>
      let' (y,A) := yA
      (y*A, fun dx =>
        (A*dx, y⊗dx))) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_A.HasRevFDeriv_rule (y : Y) :
  HasRevFDeriv R
    (fun A : M => y * A)
    (fun A => (y*A, fun dx => y⊗dx)) := sorry_proof

@[data_synth]
theorem vecMatMul.arg_x.HasRevFDeriv_rule (A : M) :
  HasRevFDeriv R
    (fun y : Y => y * A)
    (fun y => (y*A, fun dx => A*dx)) := sorry_proof


@[data_synth]
theorem vecMatMul.arg_yA.HasRevFDerivUpdate_rule :
  HasRevFDerivUpdate R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA =>
      let' (y,A) := yA
      (y*A, fun dx yA' =>
        let' (y',A') := yA'
        (matVecMulAdd (1:R) A dx (1:R) y',
         tmulAdd (1:R) y dx A'))) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_A.HasRevFDerivUpdate_rule (y : Y) :
  HasRevFDerivUpdate R
    (fun A : M => y * A)
    (fun A => (y*A, fun dx A' => tmulAdd (1:R) y dx A')) := sorry_proof

@[data_synth]
theorem vecMatMul.arg_x.HasRevFDerivUpdate_rule (A : M) :
  HasRevFDerivUpdate R
    (fun y : Y => y * A)
    (fun y => (y*A, fun dx y' => matVecMulAdd (1:R) A dx (1:R) y')) := sorry_proof
