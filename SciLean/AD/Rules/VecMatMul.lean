module

public import SciLean.Algebra.MatrixType.Basic
public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv
public import SciLean.Tactic.DataSynth.DefDataSynth
public import SciLean.Analysis.Calculus.ContDiff

@[expose] public section


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



/-- The derivative of vector-matrix multiplication in both arguments. It is the sum of the two
partial maps because the multiplication is linear in each argument separately. -/
theorem vecMatMul.arg_yA.hasFDerivAt_rule (p : Y×M) :
    HasFDerivAt (fun q : Y×M => q.1 * q.2)
      (ContinuousLinearMap.mk' R (fun dq : Y×M => dq.1 * p.2 + p.1 * dq.2) (by fun_prop)) p :=
  hasFDerivAt_of_isContinuousLinearMap_partials (f := fun (y : Y) (A : M) => y * A)
    (by fun_prop) (fun A => vecMatMul.arg_A.IsContinuousLinearMap_rule A)
    (fun y => vecMatMul.arg_x.IsContinuousLinearMap_rule y) p

@[data_synth]
theorem vecMatMul.arg_yA.HasFwdFDeriv_rule :
  HasFwdFDeriv R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA dyA =>
      let' (y,A) := yA
      let' (dy,dA) := dyA
      (y*A, vecMatMulAdd (1:R) y dA (1:R) (dy*A))) := by
  apply hasFwdFDeriv_from_hasFDerivAt (deriv := vecMatMul.arg_yA.hasFDerivAt_rule)
  intro p dp
  show (p.1 * p.2, vecMatMulAdd (1:R) p.1 dp.2 (1:R) (dp.1*p.2)) = _
  rw [vecMatMulAdd_eq_smul_add, one_smul, one_smul, add_comm]
  rfl

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_A.HasFwdFDeriv_rule (y : Y) :
  HasFwdFDeriv R
    (fun A : M => y * A)
    (fun A dA =>
      (y*A, y*dA)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
    (df := fun _ => fun A =>L[R] y * A)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (vecMatMul.arg_x.IsContinuousLinearMap_rule y))
  intros; rfl

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_x.HasFwdFDeriv_rule (A : M) :
  HasFwdFDeriv R
    (fun y : Y => y * A)
    (fun y dy =>
      (y*A, dy*A)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
    (df := fun _ => fun y =>L[R] y * A)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (vecMatMul.arg_A.IsContinuousLinearMap_rule A))
  intros; rfl


@[data_synth]
theorem vecMatMul.arg_y.HasAdjoint_rule (A : M) :
  HasAdjoint R
    (fun y : Y => y * A)
    (fun x => A * x) := sorry_proof

@[data_synth]
theorem vecMatMul.arg_y.HasAdjointUpdate_rule (A : M) :
  HasAdjointUpdate R
    (fun y : Y => y * A)
    (fun x y' => matVecMulAdd (1:R) A x (1:R) y') := by
  apply hasAdjointUpdate_from_hasAdjoint (vecMatMul.arg_y.HasAdjoint_rule A)
  intro x y'
  rw [matVecMulAdd_eq_smul_add, one_smul, one_smul, add_comm]
  rfl

@[data_synth]
theorem vecMatMul.arg_A.HasAdjoint_rule (y : Y) :
  HasAdjoint R
    (fun A : M => y * A)
    (fun x => y ⊗ x) := sorry_proof

@[data_synth]
theorem vecMatMul.arg_A.HasAdjointUpdate_rule (y : Y) :
  HasAdjointUpdate R
    (fun A : M => y * A)
    (fun x A' => tmulAdd (1:R) y x A') := by
  apply hasAdjointUpdate_from_hasAdjoint (vecMatMul.arg_A.HasAdjoint_rule y)
  intro x A'
  rw [tmulAdd_spec, one_smul, add_comm]


/-- The adjoint of the derivative of vector-matrix multiplication in both arguments. -/
theorem vecMatMul.arg_yA.hasAdjoint_deriv (p : Y×M) :
    HasAdjoint R (fun dq : Y×M => dq.1 * p.2 + p.1 * dq.2)
      (fun dx : X => (p.2 * dx, p.1 ⊗ dx)) := by
  constructor
  case adjoint =>
    intro dq dx
    rw [AdjointSpace.inner_add_left, (vecMatMul.arg_y.HasAdjoint_rule p.2).adjoint dq.1 dx,
      (vecMatMul.arg_A.HasAdjoint_rule (X:=X) p.1).adjoint dq.2 dx, AdjointSpace.inner_prod_split]
  case is_linear => fun_prop

@[data_synth]
theorem vecMatMul.arg_yA.HasRevFDeriv_rule :
  HasRevFDeriv R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA =>
      let' (y,A) := yA
      (y*A, fun dx =>
        (A*dx, y⊗dx))) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (deriv := vecMatMul.arg_yA.hasFDerivAt_rule)
    (adjoint := vecMatMul.arg_yA.hasAdjoint_deriv)
  rfl

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_A.HasRevFDeriv_rule (y : Y) :
  HasRevFDeriv R
    (fun A : M => y * A)
    (fun A => (y*A, fun dx => y⊗dx)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun _ => fun A =>L[R] y * A)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (vecMatMul.arg_x.IsContinuousLinearMap_rule y))
    (fun _ => vecMatMul.arg_A.HasAdjoint_rule y)
  rfl

@[data_synth]
theorem vecMatMul.arg_x.HasRevFDeriv_rule (A : M) :
  HasRevFDeriv R
    (fun y : Y => y * A)
    (fun y => (y*A, fun dx => A*dx)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun _ => fun y =>L[R] y * A)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (vecMatMul.arg_A.IsContinuousLinearMap_rule A))
    (fun _ => vecMatMul.arg_y.HasAdjoint_rule A)
  rfl


@[data_synth]
theorem vecMatMul.arg_yA.HasRevFDerivUpdate_rule :
  HasRevFDerivUpdate R
    (fun yA : Y×M => yA.1 * yA.2)
    (fun yA =>
      let' (y,A) := yA
      (y*A, fun dx yA' =>
        let' (y',A') := yA'
        (matVecMulAdd (1:R) A dx (1:R) y',
         tmulAdd (1:R) y dx A'))) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
    vecMatMul.arg_yA.HasRevFDeriv_rule.toHasRevFDerivUpdate
  funext yA
  simp only [Prod.mk.injEq, true_and]
  funext dx yA'
  have h1 : matVecMulAdd (1:R) yA.2 dx (1:R) yA'.1 = yA'.1 + yA.2*dx := by
    rw [matVecMulAdd_eq_smul_add, one_smul, one_smul, add_comm]; rfl
  have h2 : tmulAdd (1:R) yA.1 dx yA'.2 = yA'.2 + yA.1⊗dx := by
    rw [tmulAdd_spec, one_smul, add_comm]
  simp [h1, h2, Prod.ext_iff]

-- todo: arg subset, generate automatically
@[data_synth]
theorem vecMatMul.arg_A.HasRevFDerivUpdate_rule (y : Y) :
  HasRevFDerivUpdate R
    (fun A : M => y * A)
    (fun A => (y*A, fun dx A' => tmulAdd (1:R) y dx A')) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
    (vecMatMul.arg_A.HasRevFDeriv_rule y).toHasRevFDerivUpdate
  funext A
  simp only [Prod.mk.injEq, true_and]
  funext dx A'
  rw [tmulAdd_spec, one_smul, add_comm]

@[data_synth]
theorem vecMatMul.arg_x.HasRevFDerivUpdate_rule (A : M) :
  HasRevFDerivUpdate R
    (fun y : Y => y * A)
    (fun y => (y*A, fun dx y' => matVecMulAdd (1:R) A dx (1:R) y')) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
    (vecMatMul.arg_x.HasRevFDeriv_rule A).toHasRevFDerivUpdate
  funext y
  simp only [Prod.mk.injEq, true_and]
  funext dx y'
  rw [matVecMulAdd_eq_smul_add, one_smul, one_smul, add_comm]
  rfl
