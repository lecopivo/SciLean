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
theorem matVecMul.arg_A.IsContinuousLinearMap_rule (A : M) :
  IsContinuousLinearMap R (fun x : X => A * x) := sorry_proof

@[fun_prop]
theorem matVecMul.arg_x.IsContinuousLinearMap_rule (x : X) :
  IsContinuousLinearMap R (fun A : M => A * x) := sorry_proof

@[fun_prop]
theorem matVecMul.arg_Ax.ContDiff_rule :
  ContDiff R ⊤ (fun Ax : M×X => Ax.1 * Ax.2) := sorry_proof

-- todo: generate automatically
@[fun_prop]
theorem matVecMul.arg_Ax.Differentiable_rule :
  Differentiable R (fun Ax : M×X => Ax.1 * Ax.2) := by fun_prop

-- todo: generate automatically
@[fun_prop]
theorem matVecMul.arg_Ax.Continusous_rule :
  Continuous (fun Ax : M×X => Ax.1 * Ax.2) := by fun_prop


@[data_synth]
theorem matVecMul.arg_Ax.HasFwdFDeriv_rule :
  HasFwdFDeriv R
    (fun Ax : M×X => Ax.1 * Ax.2)
    (fun Ax dAx =>
      let' (A,x) := Ax
      let' (dA,dx) := dAx
      (A*x, matVecMulAdd (1:R) dA x (1:R) (A*dx))) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_A.HasFwdFDeriv_rule (x : X) :
  HasFwdFDeriv R
    (fun A : M => A * x)
    (fun A dA =>
      (A*x, dA*x)) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_x.HasFwdFDeriv_rule (A : M) :
  HasFwdFDeriv R
    (fun x : X => A * x)
    (fun x dx =>
      (A*x, A*dx)) := sorry_proof

@[data_synth]
theorem matVecMul.arg_x.HasAdjoint_rule (A : M) :
  HasAdjoint R
    (fun x : X => A * x)
    (fun y => y * A) := sorry_proof

@[data_synth]
theorem matVecMul.arg_x.HasAdjointUpdate_rule (A : M) :
  HasAdjointUpdate R
    (fun x : X => A * x)
    (fun y x' => vecMatMulAdd (1:R) y A (1:R) x') := sorry_proof

@[data_synth]
theorem matVecMul.arg_A.HasAdjoint_rule (x : X) :
  HasAdjoint R
    (fun A : M => A * x)
    (fun y => y ⊗ x) := sorry_proof

@[data_synth]
theorem matVecMul.arg_A.HasAdjointUpdate_rule (x : X) :
  HasAdjointUpdate R
    (fun A : M => A * x)
    (fun y A' => tmulAdd (1:R) y x A') := sorry_proof


@[data_synth]
theorem vecMatMul.arg_yA.HasRevFDeriv_rule :
  HasRevFDeriv R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA =>
      let' (y,A) := yA
      (y*A, fun dx =>
        (A*dx, y⊗dx))) := sorry_proof


@[data_synth]
theorem matVecMul.arg_Ax.HasRevFDeriv_rule :
  HasRevFDeriv R
    (fun Ax : M×X => Ax.1 * Ax.2)
    (fun Ax =>
      let' (A,x) := Ax
      (A*x, fun dy =>
        (dy⊗x, dy*A))) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_A.HasRevFDeriv_rule (x : X) :
  HasRevFDeriv R
    (fun A : M => A * x)
    (fun A => (A*x, fun dy => dy⊗x)) := sorry_proof

@[data_synth]
theorem matVecMul.arg_x.HasRevFDeriv_rule (A : M) :
  HasRevFDeriv R
    (fun x : X => A * x)
    (fun x => (A*x, fun dy => dy*A)) := sorry_proof


@[data_synth]
theorem matVecMul.arg_Ax.HasRevFDerivUpdate_rule :
  HasRevFDerivUpdate R
    (fun Ax : M×X => Ax.1 * Ax.2)
    (fun Ax =>
      let' (A,x) := Ax
      (A*x, fun dy Ax' =>
        let' (A',x') := Ax'
        (tmulAdd (1:R) dy x A',
         vecMatMulAdd (1:R) dy A (1:R) x'))) := sorry_proof

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_A.HasRevFDerivUpdate_rule (x : X) :
  HasRevFDerivUpdate R
    (fun A : M => A * x)
    (fun A => (A*x, fun dy A' => tmulAdd (1:R) dy x A')) := sorry_proof

@[data_synth]
theorem matVecMul.arg_x.HasRevFDerivUpdate_rule (A : M) :
  HasRevFDerivUpdate R
    (fun x : X => A * x)
    (fun x => (A*x, fun dy x' => vecMatMulAdd (1:R) dy A (1:R) x')) := sorry_proof
