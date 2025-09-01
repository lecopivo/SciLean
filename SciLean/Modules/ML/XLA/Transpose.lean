import SciLean.Modules.ML.XLA.TensorIndex

namespace SciLean
>
/-! StableHLO function: `transpose`

Spec: (source: https://github.com/openxla/stablehlo/blob/main/docs/spec.md)

### transpose

#### Semantics

Permutes the dimensions of `operand` tensor using `permutation` and produces a
`result` tensor. More formally, `result[result_index] = operand[operand_index]`
where `result_index[d] = operand_index[permutation[d]]`.

#### Inputs

| Label | Name          | Type                                         | Constraints |
|-------|---------------|----------------------------------------------|-------------|
| (I1)  | `operand`     | tensor or quantized tensor                   | (C1-C4)     |
| (I2)  | `permutation` | 1-dimensional tensor constant of type `si64` | (C2-C4)     |

#### Outputs

| Name     | Type                       | Constraints   |
|----------|----------------------------|---------------|
| `result` | tensor or quantized tensor | (C1), (C3-C4) |

#### Constraints

* (C1) `element_type(result)` is given by:
  * `element_type(operand)`, if `!is_per_axis_quantized(operand)`.
  * `element_type(operand)` except that `quantization_dimension(operand)` and
    `quantization_dimension(result)` may differ, otherwise.
* (C2) `permutation` is a permutation of `range(rank(operand))`.
* (C3) `shape(result) = dim(operand, permutation...)`.
* (C4) If `is_per_axis_quantized(result)`, then
  `quantization_dimension(operand) =
  permutation(quantization_dimension(result))`.

#### Examples

```mlir
// %operand: [
//            [[1,2], [3,4], [5,6]],
//            [[7,8], [9,10], [11,12]]
//           ]
%result = "stablehlo.transpose"(%operand) {
  permutation = array<i64: 2, 1, 0>
} : (tensor<2x3x2xi32>) -> tensor<2x3x2xi32>
// %result: [
//           [[1,7], [3,9], [5,11]],
//           [[2,8], [4,10], [6,12]]
//          ]
```

&nbsp;[More Examples](https://github.com/openxla/stablehlo/tree/main/stablehlo/tests/interpret/transpose.mlir)
-/


def transpose.outDims {r}
    (permutation : ArrayN ℤ r)
    (inDims : Dims r) : ArrayN ℤ r := permutation.map (λ i => inDims.get i)

def transpose {r} {inDims outDims : Dims r}
    (operand : TensorIndex inDims → R)
    (permutation : ArrayN ℤ r)
    (houtDims : outDims = transpose.outDims permutation inDims := by infer_var) :
    TensorIndex outDims → R :=
  fun result_index =>
    let operand_index := permutation.map (λ i => result_index.get i)
    operand ⟨operand_index, by intro i; have := result_index.bounds' i; simp_all[transpose.outDims]; sorry ⟩
end SciLean
