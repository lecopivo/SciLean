import SciLean.Modules.ML.XLA.TensorIndex
import Lean

namespace SciLean

/-! StableHLO function: `slice`

Spec: (source: https://github.com/openxla/stablehlo/blob/main/docs/spec.md)


### slice

#### Semantics

Extracts a slice from the `operand` using statically-computed starting indices
and produces a `result` tensor. `start_indices` contain the starting indices of
the slice for each dimension, `limit_indices` contain the ending indices
(exclusive) for the slice for each dimension, and `strides` contain the strides
for each dimension.

More formally, `result[result_index] = operand[operand_index]` where
`operand_index = start_indices + result_index * strides`.

#### Inputs

| Label | Name            | Type                                         | Constraints      |
|-------|-----------------|----------------------------------------------|------------------|
| (I1)  | `operand`       | tensor or per-tensor quantized tensor        | (C1-C3), (C5)    |
| (I2)  | `start_indices` | 1-dimensional tensor constant of type `si64` | (C2), (C3), (C5) |
| (I3)  | `limit_indices` | 1-dimensional tensor constant of type `si64` | (C2), (C3), (C5) |
| (I4)  | `strides`       | 1-dimensional tensor constant of type `si64` | (C2), (C4)       |

#### Outputs

| Name     | Type                                  | Constraints |
|----------|---------------------------------------|-------------|
| `result` | tensor or per-tensor quantized tensor | (C1), (C5)  |

#### Constraints

* (C1) `element_type(operand) = element_type(result)`.
* (C2) `size(start_indices) = size(limit_indices) = size(strides) =
  rank(operand)`.
* (C3) `0 <= start_indices <= limit_indices <= shape(operand)`.
* (C4) `0 < strides`.
* (C5) `shape(result) = ceil((limit_indices - start_indices) / strides)`.

#### Examples

```mlir
// %operand: [
//            [0, 0, 0, 0],
//            [0, 0, 1, 1],
//            [0, 0, 1, 1]
//           ]
%result = "stablehlo.slice"(%operand) {
  start_indices = array<i64: 1, 2>,
  limit_indices = array<i64: 3, 4>,
  strides = array<i64: 1, 1>
} : (tensor<3x4xi64>) -> tensor<2x2xi64>
// % result: [
//            [1, 1],
//            [1, 1]
//           ]
```

&nbsp;[More Examples](https://github.com/openxla/stablehlo/tree/main/stablehlo/tests/interpret/slice.mlir)

-/

namespace Slice

def slice.outShape {r}
    (start_indices limit_indices : ArrayN ℤ r)
    (strides : ArrayN ℕ+ r) : ArrayN ℤ r :=
      .ofFn fun i => Rat.ceil <|
        (Rat.ofInt (limit_indices[i] - start_indices[i])) / (Rat.ofInt (Int.ofNat (strides[i])))
        -- this should be equal to which might be easier to reason about
        -- (limit_indices[i] - start_indices[i] + (strides[i] - 1)).fdiv strides[i]

structure Args {r} (inDims : Dims r) where
  start_indices : ArrayN ℤ r
  limit_indices : ArrayN ℤ r
  strides : ArrayN ℕ+ r

def Args.outShape {r} {inDims : Dims r} (args : Args inDims) : Dims r :=
      .ofFn fun i => Rat.ceil <|
        (Rat.ofInt (args.limit_indices[i] - args.start_indices[i])) / (Rat.ofInt (Int.ofNat (args.strides[i])))
        -- this should be equal to which might be easier to reason about
        -- (limit_indices[i] - start_indices[i] + (strides[i] - 1)).fdiv strides[i]

structure Preconditions {r} {inDims : Dims r} (args : Args inDims) where
  c1 : True
  c2 : args.start_indices.size = r ∧ args.limit_indices.size = r ∧ args.strides.size = r ∧ inDims.size = r
  c3 : ∀ d, 0 ≤ args.start_indices[d] ∧ args.start_indices[d] ≤ args.limit_indices[d]
  c4 : 0 < args.strides.toNat

structure Postconditions {r} {inDims : Dims r} (args : Args inDims) (outDims : Dims r) where
  c5 : outDims = args.outShape

end Slice

open Slice in
def slice
    {r} {inDims outDims : Dims r}
    (operand : TensorIndex inDims → R)
    (args : Args inDims)
    (h : Preconditions args)
    (houtDims : outDims = args.outShape := by infer_var) :
    TensorIndex outDims → R :=
  fun result_index =>
    let operand_index := args.start_indices + result_index.1 * args.strides
    operand ⟨operand_index, by
      intro i
      have h := h.c3 i
      have h' := result_index.2 i
      simp [operand_index]
      constructor;
      · have := h.1; have := h'.1; positivity
      · have := h.2; have := h'.2; simp_all[houtDims]; sorry⟩
