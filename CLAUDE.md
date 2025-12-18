# SciLean Development Guidelines

## Project Philosophy
**Verification and sorry-free is NOT the point of this repo!** This is a scientific computing library focused on practical functionality. Technical debt via `sorry_proof` is acceptable. Priorities:
1. Keep up with Lean 4 releases (currently v4.26)
2. BLAS benchmarks and performance
3. Gradient/autodiff tests
4. Better ML support (see lean-mlir for inspiration)

## Backend Architecture (Future)
SciLean uses dependent types (`Float^[784]`, `Float^[128, 784]`) wrapping compute backends:

```
┌──────────────────────────────────────────────┐
│  SciLean Dependent Types + Autodiff          │
│  DataArrayN, gradients, fun_trans            │
└──────────────────────────────────────────────┘
                     │
                     ▼
┌──────────────────────────────────────────────┐
│  Backend Typeclass (TensorBackend)           │
│  gemm, axpy, softmax, conv2d, ...            │
└──────────────────────────────────────────────┘
       │            │            │
       ▼            ▼            ▼
   ┌───────┐   ┌────────┐   ┌────────┐
   │ BLAS  │   │ Metal  │   │ CUDA   │
   │ (CPU) │   │ (MPS)  │   │(future)│
   └───────┘   └────────┘   └────────┘
```

**Current state:**
- LeanBLAS: BLAS Level 1-3 bindings (CPU) ✅
- Metal: Started in `SciLean/FFI/Metal.lean` ✅
- CUDA: Not started

**Related projects:**
- [TensorLib](https://github.com/leanprover/TensorLib): Verified tensors, .npy file support (steal this!)
- [c-libtorch](https://github.com/lighttransport/c-libtorch): C bindings to PyTorch (minimal, needs work)
- [tch-rs](https://github.com/LaurentMazare/tch-rs): Rust libtorch bindings (reference for API design)
- [Hasktorch](https://github.com/hasktorch/hasktorch): Haskell libtorch bindings

## Local Dependencies
- **LeanBLAS** (`../LeanBLAS`): Vendored locally for active development. Expect frequent changes to BLAS bindings, Level 1-3 operations, and FFI layer. Keep in sync with SciLean's mathlib version.
- **LeanPlot** (`../LeanPlot`): Local visualization library

## Build Commands
- Build entire project: `lake build`
- Run tests: `lake test`
- Test a specific file: `lake build Test.file_name` (e.g., `lake build Test.calculus.revFDeriv_test`)
- Run an example: `lake build ExampleName && .lake/build/bin/ExampleName` (e.g., `lake build HarmonicOscillator && .lake/build/bin/HarmonicOscillator`)

## Code Style Guidelines
- **Indentation**: 2 spaces
- **Naming**: CamelCase for types/classes, snake_case for variables, Unicode for mathematical symbols
- **Imports**: Organized at top by dependency, open primary namespace
- **Types**: Use typeclasses for mathematical abstractions, explicit type constraints where needed
- **Documentation**: `/--` blocks with markdown, mathematical notation where appropriate
- **Attributes**: Use `@[simp]`, `@[fun_trans]`, `@[data_synth]` for optimization rules
- **Error handling**: Use dependent types and type constraints over runtime checks

## Conventions
- Proofs use the `by` syntax with tactic blocks
- Mathematical properties follow the theorem naming pattern `operation.arg_name.property_rule`
- Make heavy use of metaprogramming for tactics and automation
- Clear distinction between forward and reverse mode differentiation in naming
- Add existing imports as comments when disabling them

## TODO (for future sessions)
- Reenable doc.verso

## Lean 4 Tips
- **Float infinity**: Lean 4 stdlib doesn't have `Float.inf`. Define as:
  ```lean
  def Float.inf : Float := 1.0 / 0.0
  def Float.negInf : Float := -1.0 / 0.0
  ```
  These are proper IEEE 754 infinity values for min/max tracking.

  ---

  use lean-lsp-mcp hover on nested src code after writing it to ENSURE its in
  the right namespace. like `Float.inf` may need to be `_root_.Float.inf`.
