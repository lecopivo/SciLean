module

public import SciLean.Algebra.MatrixType.Basic
public import SciLean.Analysis.Calculus.HasRevFDeriv
public import SciLean.Analysis.Calculus.HasFwdFDeriv
public import SciLean.Tactic.DataSynth.DefDataSynth
public import SciLean.Analysis.Calculus.ContDiff
public import SciLean.AD.Rules.VecMatMul

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
theorem matVecMul.arg_A.IsContinuousLinearMap_rule (A : M) :
  IsContinuousLinearMap R (fun x : X => A * x) :=
  (vecMatMul.arg_y.HasAdjoint_rule A).isContinuousLinearMap'

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


/-- The derivative of matrix-vector multiplication in both arguments. It is the sum of the two
partial maps because the multiplication is linear in each argument separately. -/
theorem matVecMul.arg_Ax.hasFDerivAt_rule (p : M×X) :
    HasFDerivAt (fun q : M×X => q.1 * q.2)
      (ContinuousLinearMap.mk' R (fun dq : M×X => dq.1 * p.2 + p.1 * dq.2) (by fun_prop)) p :=
  hasFDerivAt_of_isContinuousLinearMap_partials (f := fun (A : M) (x : X) => A * x)
    (by fun_prop) (fun x => matVecMul.arg_x.IsContinuousLinearMap_rule x)
    (fun A => matVecMul.arg_A.IsContinuousLinearMap_rule A) p

@[data_synth]
theorem matVecMul.arg_Ax.HasFwdFDeriv_rule :
  HasFwdFDeriv R
    (fun Ax : M×X => Ax.1 * Ax.2)
    (fun Ax dAx =>
      let' (A,x) := Ax
      let' (dA,dx) := dAx
      (A*x, matVecMulAdd (1:R) dA x (1:R) (A*dx))) := by
  apply hasFwdFDeriv_from_hasFDerivAt (deriv := matVecMul.arg_Ax.hasFDerivAt_rule)
  intro p dp
  show (p.1 * p.2, matVecMulAdd (1:R) dp.1 p.2 (1:R) (p.1*dp.2)) = _
  rw [matVecMulAdd_eq_smul_add, one_smul, one_smul]
  rfl

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_A.HasFwdFDeriv_rule (x : X) :
  HasFwdFDeriv R
    (fun A : M => A * x)
    (fun A dA =>
      (A*x, dA*x)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
    (df := fun _ => fun A =>L[R] A * x)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (matVecMul.arg_x.IsContinuousLinearMap_rule x))
  intros; rfl

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_x.HasFwdFDeriv_rule (A : M) :
  HasFwdFDeriv R
    (fun x : X => A * x)
    (fun x dx =>
      (A*x, A*dx)) := by
  apply hasFwdFDeriv_from_hasFDerivAt
    (df := fun _ => fun x =>L[R] A * x)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (matVecMul.arg_A.IsContinuousLinearMap_rule A))
  intros; rfl

@[data_synth]
theorem matVecMul.arg_x.HasAdjoint_rule (A : M) :
  HasAdjoint R
    (fun x : X => A * x)
    (fun y => y * A) := by
  constructor
  · intro x y
    rw [← AdjointSpace.conj_symm, ← (vecMatMul.arg_y.HasAdjoint_rule A).adjoint,
      AdjointSpace.conj_symm]
  · exact matVecMul.arg_A.IsContinuousLinearMap_rule A

@[data_synth]
theorem matVecMul.arg_x.HasAdjointUpdate_rule (A : M) :
  HasAdjointUpdate R
    (fun x : X => A * x)
    (fun y x' => vecMatMulAdd (1:R) y A (1:R) x') := by
  apply hasAdjointUpdate_from_hasAdjoint (matVecMul.arg_x.HasAdjoint_rule A)
  intro y x'
  rw [vecMatMulAdd_eq_smul_add, one_smul, one_smul, add_comm]
  rfl

@[data_synth]
theorem matVecMul.arg_A.HasAdjoint_rule (x : X) :
  HasAdjoint R
    (fun A : M => A * x)
    (fun y => y ⊗ x) := sorry_proof

@[data_synth]
theorem matVecMul.arg_A.HasAdjointUpdate_rule (x : X) :
  HasAdjointUpdate R
    (fun A : M => A * x)
    (fun y A' => tmulAdd (1:R) y x A') := by
  apply hasAdjointUpdate_from_hasAdjoint (matVecMul.arg_A.HasAdjoint_rule x)
  intro y A'
  rw [tmulAdd_spec, one_smul, add_comm]


-- `vecMatMul.arg_yA.HasRevFDeriv_rule` is stated and proved in `SciLean.AD.Rules.VecMatMul`
-- (imported above); it used to be duplicated here with a `sorry_proof`.

/-- The adjoint of the derivative of matrix-vector multiplication in both arguments. -/
theorem matVecMul.arg_Ax.hasAdjoint_deriv (p : M×X) :
    HasAdjoint R (fun dq : M×X => dq.1 * p.2 + p.1 * dq.2)
      (fun dy : Y => (dy ⊗ p.2, dy * p.1)) := by
  constructor
  case adjoint =>
    intro dq dy
    rw [AdjointSpace.inner_add_left, (matVecMul.arg_A.HasAdjoint_rule (M:=M) p.2).adjoint dq.1 dy,
      (matVecMul.arg_x.HasAdjoint_rule p.1).adjoint dq.2 dy, AdjointSpace.inner_prod_split]
  case is_linear => fun_prop

@[data_synth]
theorem matVecMul.arg_Ax.HasRevFDeriv_rule :
  HasRevFDeriv R
    (fun Ax : M×X => Ax.1 * Ax.2)
    (fun Ax =>
      let' (A,x) := Ax
      (A*x, fun dy =>
        (dy⊗x, dy*A))) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (deriv := matVecMul.arg_Ax.hasFDerivAt_rule)
    (adjoint := matVecMul.arg_Ax.hasAdjoint_deriv)
  rfl

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_A.HasRevFDeriv_rule (x : X) :
  HasRevFDeriv R
    (fun A : M => A * x)
    (fun A => (A*x, fun dy => dy⊗x)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun _ => fun A =>L[R] A * x)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (matVecMul.arg_x.IsContinuousLinearMap_rule x))
    (fun _ => matVecMul.arg_A.HasAdjoint_rule x)
  rfl

@[data_synth]
theorem matVecMul.arg_x.HasRevFDeriv_rule (A : M) :
  HasRevFDeriv R
    (fun x : X => A * x)
    (fun x => (A*x, fun dy => dy*A)) := by
  apply hasRevFDeriv_from_hasFDerivAt_hasAdjoint
    (df := fun _ => fun x =>L[R] A * x)
    (fun _ => hasFDerivAt_from_isContinuousLinearMap
      (matVecMul.arg_A.IsContinuousLinearMap_rule A))
    (fun _ => matVecMul.arg_x.HasAdjoint_rule A)
  rfl


@[data_synth]
theorem matVecMul.arg_Ax.HasRevFDerivUpdate_rule :
  HasRevFDerivUpdate R
    (fun Ax : M×X => Ax.1 * Ax.2)
    (fun Ax =>
      let' (A,x) := Ax
      (A*x, fun dy Ax' =>
        let' (A',x') := Ax'
        (tmulAdd (1:R) dy x A',
         vecMatMulAdd (1:R) dy A (1:R) x'))) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
    matVecMul.arg_Ax.HasRevFDeriv_rule.toHasRevFDerivUpdate
  funext Ax
  simp only [Prod.mk.injEq, true_and]
  funext dy Ax'
  have h1 : tmulAdd (1:R) dy Ax.2 Ax'.1 = Ax'.1 + dy⊗Ax.2 := by
    rw [tmulAdd_spec, one_smul, add_comm]
  have h2 : vecMatMulAdd (1:R) dy Ax.1 (1:R) Ax'.2 = Ax'.2 + dy*Ax.1 := by
    rw [vecMatMulAdd_eq_smul_add, one_smul, one_smul, add_comm]; rfl
  simp [h1, h2, Prod.ext_iff]

-- todo: arg subset, generate automatically
@[data_synth]
theorem matVecMul.arg_A.HasRevFDerivUpdate_rule (x : X) :
  HasRevFDerivUpdate R
    (fun A : M => A * x)
    (fun A => (A*x, fun dy A' => tmulAdd (1:R) dy x A')) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
    (matVecMul.arg_A.HasRevFDeriv_rule x).toHasRevFDerivUpdate
  funext A
  simp only [Prod.mk.injEq, true_and]
  funext dy A'
  rw [tmulAdd_spec, one_smul, add_comm]

@[data_synth]
theorem matVecMul.arg_x.HasRevFDerivUpdate_rule (A : M) :
  HasRevFDerivUpdate R
    (fun x : X => A * x)
    (fun x => (A*x, fun dy x' => vecMatMulAdd (1:R) dy A (1:R) x')) := by
  apply hasRevFDerivUpdate_from_hasRevFDerivUpdate
    (matVecMul.arg_x.HasRevFDeriv_rule A).toHasRevFDerivUpdate
  funext x
  simp only [Prod.mk.injEq, true_and]
  funext dy x'
  rw [vecMatMulAdd_eq_smul_add, one_smul, one_smul, add_comm]
  rfl
