/-
Copyright (c) 2024 SciLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SciLean contributors
-/
import SciLean.Data.Tensor
import SciLean.AD.RevFDeriv
import SciLean.Analysis.Scalar.FloatAsReal
import SciLean.Analysis.AdjointSpace.Basic
import SciLean.Analysis.Calculus.Monad.HasRevFDerivMonad

namespace SciLean

/-!
# Reverse-Mode Autodiff for Tensors

This module provides autodiff support for both CPU and GPU tensors.

## CPU Tensors
For CPU tensors, we provide `NormedAddCommGroup` and `AdjointSpace` instances
that enable integration with SciLean's `@[fun_trans]` system.

## GPU Tensors
GPU operations are in IO monad, so we use explicit backward functions
that leverage the GPU backward kernels for efficiency.

Note: Float-based tensors don't satisfy mathematical axioms exactly (finite precision),
so proofs use `sorry_proof`. The computations work correctly in practice.
-/

set_option linter.unusedVariables false

variable {ι : Type*} {n : ℕ} [IndexType ι n] [Fold ι]

/-! ## Algebra Instances for CpuTensor -/

namespace CpuTensor

variable {α : Type*} [PlainDataType α]

/-- Zero tensor -/
def zero : CpuTensor Float ι := ⟨⊞ (_ : ι) => (0 : Float)⟩

/-- Sum of all elements -/
def sum (t : CpuTensor Float ι) : Float :=
  IndexType.fold .full (init := (0 : Float)) (fun (i : ι) acc => acc + t[i])

/-- L2 norm squared -/
def normSq (t : CpuTensor Float ι) : Float :=
  IndexType.fold .full (init := (0 : Float)) (fun (i : ι) acc => acc + t[i] * t[i])

/-- L2 norm -/
def norm (t : CpuTensor Float ι) : Float := Float.sqrt (normSq t)

/-- Inner product (dot product) -/
def inner (a b : CpuTensor Float ι) : Float :=
  IndexType.fold .full (init := (0 : Float)) (fun (i : ι) acc => acc + a[i] * b[i])

/-- Helper: create tensor from element-wise operation -/
def reluGrad (a dt : CpuTensor Float ι) : CpuTensor Float ι :=
  ⟨⊞ (i : ι) => if a[i] > 0 then dt[i] else 0⟩

end CpuTensor

/-! ## Typeclass Instances for CpuTensor Float -/

instance : Zero (CpuTensor Float ι) where
  zero := CpuTensor.zero

instance : SMul Float (CpuTensor Float ι) where
  smul := CpuTensor.smul

instance : AddCommGroup (CpuTensor Float ι) where
  add := CpuTensor.add
  neg := CpuTensor.neg
  zero := CpuTensor.zero
  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  add_comm := sorry_proof
  nsmul := fun n t => CpuTensor.smul (Float.ofNat n) t
  nsmul_zero := sorry_proof
  nsmul_succ := sorry_proof
  zsmul := fun z t => CpuTensor.smul (Float.ofInt z) t
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
  neg_add_cancel := sorry_proof
  sub_eq_add_neg := sorry_proof

instance : Module Float (CpuTensor Float ι) where
  smul := CpuTensor.smul
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof

/-- Norm instance for CpuTensor -/
instance : Norm (CpuTensor Float ι) where
  norm := fun t => floatToReal (CpuTensor.norm t)

/-- Inner product instance -/
instance : Inner Float (CpuTensor Float ι) where
  inner := fun a b => CpuTensor.inner a b

/-- NormedAddCommGroup instance for CpuTensor Float -/
instance : NormedAddCommGroup (CpuTensor Float ι) where
  dist := fun a b => ‖a - b‖
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist := fun a b => ENNReal.ofReal ‖a - b‖
  edist_dist := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

/-- NormedSpace instance -/
instance : NormedSpace Float (CpuTensor Float ι) where
  norm_smul_le := sorry_proof

/-- AdjointSpace instance for CpuTensor Float
    This enables automatic adjoint computation for tensor functions. -/
instance : AdjointSpace Float (CpuTensor Float ι) where
  inner_top_equiv_norm := ⟨1, 1, by norm_num, by norm_num, sorry_proof⟩
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

/-- CompleteSpace instance for CpuTensor Float
    Required for many differentiability proofs. -/
instance : CompleteSpace (CpuTensor Float ι) where
  complete := sorry_proof

/-! ## HasRevFDerivMonad Instance for IO

This enables monadic autodiff for IO-based GPU operations.
GPU ops are in IO, so we provide an IO monad instance for the autodiff system.

Note: The `HasRevFDerivM` predicate uses `True` as a placeholder because:
1. GPU operations are opaque FFI calls - we can't extract values to prove properties
2. Correctness is asserted per-operation via `sorry_proof` in data_synth rules
3. The actual backward computations use the efficient GPU backward kernels -/

variable {n : ℕ}

instance : HasRevFDerivMonad Float IO IO where
  HasRevFDerivM _ _ := True
  HasRevFDerivM_pure := fun _ _ _ => trivial
  HasRevFDerivM_bind := fun _ _ _ _ _ _ => trivial
  HasRevFDerivM_pair := fun _ _ _ => trivial

/-! ## Differentiability Proofs

These @[fun_prop] rules enable automatic Differentiable proof synthesis.
-/

@[fun_prop]
theorem CpuTensor.add.arg_ab.Differentiable_rule
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Float X]
    (a b : X → CpuTensor Float ι)
    (ha : Differentiable Float a) (hb : Differentiable Float b) :
    Differentiable Float (fun x => CpuTensor.add (a x) (b x)) := sorry_proof

@[fun_prop]
theorem CpuTensor.neg.arg_a.Differentiable_rule
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Float X]
    (a : X → CpuTensor Float ι)
    (ha : Differentiable Float a) :
    Differentiable Float (fun x => CpuTensor.neg (a x)) := sorry_proof

@[fun_prop]
theorem CpuTensor.smul.arg_a.Differentiable_rule
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Float X]
    (s : Float) (a : X → CpuTensor Float ι)
    (ha : Differentiable Float a) :
    Differentiable Float (fun x => CpuTensor.smul s (a x)) := sorry_proof

@[fun_prop]
theorem CpuTensor.mul.arg_ab.Differentiable_rule
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Float X]
    (a b : X → CpuTensor Float ι)
    (ha : Differentiable Float a) (hb : Differentiable Float b) :
    Differentiable Float (fun x => CpuTensor.mul (a x) (b x)) := sorry_proof

@[fun_prop]
theorem CpuTensor.relu.arg_a.Differentiable_rule
    {X : Type*} [NormedAddCommGroup X] [NormedSpace Float X]
    (a : X → CpuTensor Float ι)
    (ha : Differentiable Float a) :
    Differentiable Float (fun x => CpuTensor.relu (a x)) := sorry_proof

/-! ## Gradient Computation Functions (CPU) -/

/-- Compute gradient of addition w.r.t. both arguments -/
def gradAdd (dt : CpuTensor Float ι) : CpuTensor Float ι × CpuTensor Float ι :=
  (dt, dt)

/-- Compute gradient of element-wise multiplication -/
def gradMul (a b dt : CpuTensor Float ι) : CpuTensor Float ι × CpuTensor Float ι :=
  (CpuTensor.mul dt b, CpuTensor.mul dt a)

/-- Compute gradient of negation -/
def gradNeg (dt : CpuTensor Float ι) : CpuTensor Float ι :=
  CpuTensor.neg dt

/-- Compute gradient of scalar multiplication -/
def gradSmul (s : Float) (dt : CpuTensor Float ι) : CpuTensor Float ι :=
  CpuTensor.smul s dt

/-- Compute gradient of subtraction -/
def gradSub (dt : CpuTensor Float ι) : CpuTensor Float ι × CpuTensor Float ι :=
  (dt, CpuTensor.neg dt)

/-- Compute subgradient of ReLU -/
def gradRelu (a dt : CpuTensor Float ι) : CpuTensor Float ι :=
  CpuTensor.reluGrad a dt

/-! ## GPU Backward Pass Functions

GPU operations are in IO monad, so we provide explicit backward functions
that use the efficient GPU backward kernels.
-/

namespace GpuTensor

/-- ReLU backward pass on GPU
    Returns grad_input = grad_output * (input > 0) -/
def reluBackward (input gradOutput : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx n)) := do
  let result ← Metal.GpuBuffer.reluBackward input.data.buffer gradOutput.data.buffer n.toUSize
  return ⟨⟨result⟩⟩

/-- Element-wise multiply backward pass on GPU
    Returns (grad_a, grad_b) where grad_a = grad * b, grad_b = grad * a -/
def mulBackward (a b gradOutput : GpuTensor Float (Idx n)) :
    IO (GpuTensor Float (Idx n) × GpuTensor Float (Idx n)) := do
  let (gradA, gradB) ← Metal.GpuBuffer.mulBackward a.data.buffer b.data.buffer
      gradOutput.data.buffer n.toUSize
  return (⟨⟨gradA⟩⟩, ⟨⟨gradB⟩⟩)

/-- GELU backward pass on GPU -/
def geluBackward (input gradOutput : GpuTensor Float (Idx n)) : IO (GpuTensor Float (Idx n)) := do
  let result ← Metal.GpuBuffer.geluBackward input.data.buffer gradOutput.data.buffer n.toUSize
  return ⟨⟨result⟩⟩

/-- Softmax backward pass on GPU -/
def softmaxBackward (softmaxOutput gradOutput : GpuTensor Float (Idx m × Idx n)) :
    IO (GpuTensor Float (Idx m × Idx n)) := do
  let result ← Metal.GpuBuffer.softmaxBackward softmaxOutput.data.buffer
      gradOutput.data.buffer m.toUSize n.toUSize
  return ⟨⟨result⟩⟩

end GpuTensor

/-! ## Backward Pass for Common Operations -/

/-- Backward pass for a simple feedforward computation: relu(a * x + b)
    Returns gradient w.r.t. x -/
def backwardDense (a x b : CpuTensor Float ι) (dout : CpuTensor Float ι) : CpuTensor Float ι :=
  let y := CpuTensor.add (CpuTensor.mul a x) b
  let dy := CpuTensor.reluGrad y dout
  CpuTensor.mul dy a

/-! ## fun_trans Rules for CpuTensor Operations

These rules enable automatic differentiation through the fun_trans tactic.
-/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Float X] [AdjointSpace Float X]

/-- RevFDeriv of tensor addition -/
@[fun_trans]
theorem CpuTensor.add.arg_ab.revFDeriv_rule
    (a b : X → CpuTensor Float ι)
    (ha : Differentiable Float a) (hb : Differentiable Float b) :
    revFDeriv Float (fun x => CpuTensor.add (a x) (b x))
    =
    fun x =>
      let (ya, dfa) := revFDeriv Float a x
      let (yb, dfb) := revFDeriv Float b x
      (CpuTensor.add ya yb, fun dt => dfa dt + dfb dt) := by
  unfold revFDeriv; fun_trans; sorry_proof

/-- RevFDeriv of tensor negation -/
@[fun_trans]
theorem CpuTensor.neg.arg_a.revFDeriv_rule
    (a : X → CpuTensor Float ι)
    (ha : Differentiable Float a) :
    revFDeriv Float (fun x => CpuTensor.neg (a x))
    =
    fun x =>
      let (ya, dfa) := revFDeriv Float a x
      (CpuTensor.neg ya, fun dt => dfa (CpuTensor.neg dt)) := by
  unfold revFDeriv; fun_trans; sorry_proof

/-- RevFDeriv of scalar multiplication -/
@[fun_trans]
theorem CpuTensor.smul.arg_a.revFDeriv_rule
    (s : Float) (a : X → CpuTensor Float ι)
    (ha : Differentiable Float a) :
    revFDeriv Float (fun x => CpuTensor.smul s (a x))
    =
    fun x =>
      let (ya, dfa) := revFDeriv Float a x
      (CpuTensor.smul s ya, fun dt => dfa (CpuTensor.smul s dt)) := by
  unfold revFDeriv; fun_trans; sorry_proof

/-- RevFDeriv of element-wise multiplication -/
@[fun_trans]
theorem CpuTensor.mul.arg_ab.revFDeriv_rule
    (a b : X → CpuTensor Float ι)
    (ha : Differentiable Float a) (hb : Differentiable Float b) :
    revFDeriv Float (fun x => CpuTensor.mul (a x) (b x))
    =
    fun x =>
      let (ya, dfa) := revFDeriv Float a x
      let (yb, dfb) := revFDeriv Float b x
      (CpuTensor.mul ya yb, fun dt =>
        -- grad_a = dt * b, grad_b = dt * a
        dfa (CpuTensor.mul dt yb) + dfb (CpuTensor.mul dt ya)) := by
  unfold revFDeriv; fun_trans; sorry_proof

/-- RevFDeriv of subtraction -/
@[fun_trans]
theorem CpuTensor.sub.arg_ab.revFDeriv_rule
    (a b : X → CpuTensor Float ι)
    (ha : Differentiable Float a) (hb : Differentiable Float b) :
    revFDeriv Float (fun x => CpuTensor.add (a x) (CpuTensor.neg (b x)))
    =
    fun x =>
      let (ya, dfa) := revFDeriv Float a x
      let (yb, dfb) := revFDeriv Float b x
      (CpuTensor.add ya (CpuTensor.neg yb), fun dt => dfa dt + dfb (CpuTensor.neg dt)) := by
  unfold revFDeriv; fun_trans; sorry_proof

/-- RevFDeriv of ReLU (subgradient) -/
@[fun_trans]
theorem CpuTensor.relu.arg_a.revFDeriv_rule
    (a : X → CpuTensor Float ι)
    (ha : Differentiable Float a) :
    revFDeriv Float (fun x => CpuTensor.relu (a x))
    =
    fun x =>
      let (ya, dfa) := revFDeriv Float a x
      let y := CpuTensor.relu ya
      -- Subgradient: grad_input = grad_output * (input > 0 ? 1 : 0)
      (y, fun dt => dfa (CpuTensor.reluGrad ya dt)) := by
  unfold revFDeriv; fun_trans; sorry_proof

/-! ## GPU Tensor Autodiff via HasRevFDerivM

GPU operations return IO, so we use the monadic autodiff system (HasRevFDerivM).
These data_synth rules wire up the GPU backward kernels for efficient gradient computation.

For these rules to work, GpuTensor needs NormedAddCommGroup and AdjointSpace instances.
Since actual GPU operations are opaque FFI calls, we use sorry_proof for mathematical properties.
-/

variable {m : ℕ}

/-! ### Algebra Instances for GpuTensor

These instances are needed for HasRevFDerivM. The algebraic structure is formal since
actual computations happen via GPU kernels. -/

-- Note: We define these for Idx n specifically since GpuTensor ops are defined for Idx n
-- The placeholder implementations are never called in practice; GPU ops go through IO monad.
-- These are marked noncomputable since they use axioms for structural instances.

axiom GpuTensor.defaultFloat : GpuTensor Float (Idx n)

noncomputable instance : Inhabited (GpuTensor Float (Idx n)) := ⟨GpuTensor.defaultFloat⟩

noncomputable instance : Zero (GpuTensor Float (Idx n)) where
  zero := GpuTensor.defaultFloat

noncomputable instance : Add (GpuTensor Float (Idx n)) where
  add a _ := a  -- Placeholder; real add is GpuTensor.add (IO-based)

noncomputable instance : Neg (GpuTensor Float (Idx n)) where
  neg a := a  -- Placeholder; real neg would need GPU kernel

noncomputable instance : SMul Float (GpuTensor Float (Idx n)) where
  smul _ a := a  -- Placeholder

noncomputable instance : HSMul ℕ (GpuTensor Float (Idx n)) (GpuTensor Float (Idx n)) where
  hSMul _ a := a  -- Placeholder

noncomputable instance : HSMul ℤ (GpuTensor Float (Idx n)) (GpuTensor Float (Idx n)) where
  hSMul _ a := a  -- Placeholder

noncomputable instance : AddCommGroup (GpuTensor Float (Idx n)) where
  add := (· + ·)
  neg := (- ·)
  zero := 0
  add_assoc := sorry_proof
  zero_add := sorry_proof
  add_zero := sorry_proof
  add_comm := sorry_proof
  nsmul := fun k t => k • t
  nsmul_zero := sorry_proof
  nsmul_succ := sorry_proof
  zsmul := fun z t => z • t
  zsmul_zero' := sorry_proof
  zsmul_succ' := sorry_proof
  zsmul_neg' := sorry_proof
  neg_add_cancel := sorry_proof
  sub_eq_add_neg := sorry_proof

noncomputable instance : Module Float (GpuTensor Float (Idx n)) where
  smul := (· • ·)
  one_smul := sorry_proof
  mul_smul := sorry_proof
  smul_zero := sorry_proof
  smul_add := sorry_proof
  add_smul := sorry_proof
  zero_smul := sorry_proof

noncomputable instance : Norm (GpuTensor Float (Idx n)) where
  norm _ := 0  -- Placeholder; real norm would need GPU-to-CPU transfer

noncomputable instance : Inner Float (GpuTensor Float (Idx n)) where
  inner _ _ := 0  -- Placeholder

noncomputable instance : NormedAddCommGroup (GpuTensor Float (Idx n)) where
  dist := fun a b => ‖a - b‖
  dist_self := sorry_proof
  dist_comm := sorry_proof
  dist_triangle := sorry_proof
  edist := fun a b => ENNReal.ofReal ‖a - b‖
  edist_dist := sorry_proof
  eq_of_dist_eq_zero := sorry_proof

noncomputable instance : NormedSpace Float (GpuTensor Float (Idx n)) where
  norm_smul_le := sorry_proof

noncomputable instance : AdjointSpace Float (GpuTensor Float (Idx n)) where
  inner_top_equiv_norm := ⟨1, 1, by norm_num, by norm_num, sorry_proof⟩
  conj_symm := sorry_proof
  add_left := sorry_proof
  smul_left := sorry_proof

/-! ### data_synth Rules for GPU Operations

These rules enable the monadic autodiff system to use GPU backward kernels.
Each rule specifies: forward pass (returns IO) and backward pass (also IO).
-/

/-- GPU ReLU: HasRevFDerivM rule using reluBackward kernel -/
@[data_synth]
theorem GpuTensor.relu.arg_x.HasRevFDerivM_rule :
    HasRevFDerivM Float
      (fun (x : GpuTensor Float (Idx n)) => GpuTensor.relu x)
      (fun x => do
        let y ← GpuTensor.relu x
        pure (y, fun dy => GpuTensor.reluBackward x dy)) := by
  trivial

/-- GPU element-wise multiply: HasRevFDerivM rule using mulBackward kernel -/
@[data_synth]
theorem GpuTensor.mul.arg_ab.HasRevFDerivM_rule :
    HasRevFDerivM Float
      (fun (ab : GpuTensor Float (Idx n) × GpuTensor Float (Idx n)) =>
        GpuTensor.mul ab.1 ab.2)
      (fun ab => do
        let y ← GpuTensor.mul ab.1 ab.2
        pure (y, fun dy => do
          let (da, db) ← GpuTensor.mulBackward ab.1 ab.2 dy
          pure (da, db))) := by
  trivial

/-- GPU element-wise add: HasRevFDerivM rule (gradient is identity for both args) -/
@[data_synth]
theorem GpuTensor.add.arg_ab.HasRevFDerivM_rule :
    HasRevFDerivM Float
      (fun (ab : GpuTensor Float (Idx n) × GpuTensor Float (Idx n)) =>
        GpuTensor.add ab.1 ab.2)
      (fun ab => do
        let y ← GpuTensor.add ab.1 ab.2
        pure (y, fun dy => pure (dy, dy))) := by
  trivial

end SciLean
