import SciLean.Modules.ML.XLA.TensorIndex

/-!

### concatenate

#### Semantics

Concatenates `inputs` along `dimension` dimension in the same order as the given
arguments and produces a `result` tensor. More formally,
`result[i0, ..., id, ..., iR-1] = inputs[k][i0, ..., kd, ..., iR-1]`, where:

1. `id = d0 + ... + dk-1 + kd`.
1. `d` is equal to `dimension`, and `d0`, ... are `d`th dimension sizes
   of `inputs`.

#### Inputs

| Label | Name        | Type                                                       | Constraints      |
|-------|-------------|------------------------------------------------------------|------------------|
| (I1)  | `inputs`    | variadic number of tensors or per-tensor quantized tensors | (C1-C6)          |
| (I2)  | `dimension` | constant of type `si64`                                    | (C2), (C4), (C6) |

#### Outputs

| Name     | Type                                  | Constraints |
|----------|---------------------------------------|-------------|
| `result` | tensor or per-tensor quantized tensor | (C5-C6)     |

#### Constraints

* (C1) `same(element_type(inputs...))`.
* (C2) `same(shape(inputs...))` except for `dim(inputs..., dimension)`.
* (C3) `0 < size(inputs)`.
* (C4) `0 <= dimension < rank(inputs[0])`.
* (C5) `element_type(result) = element_type(inputs[0])`.
* (C6) `shape(result) = shape(inputs[0])` except for:
  * `dim(result, dimension) = dim(inputs[0], dimension) + ...`.

#### Examples

```mlir
// %input0: [[1, 2], [3, 4], [5, 6]]
// %input1: [[7, 8]]
%result = "stablehlo.concatenate"(%input0, %input1) {
  dimension = 0 : i64
} : (tensor<3x2xi64>, tensor<1x2xi64>) -> tensor<4x2xi64>
// %result: [[1, 2], [3, 4], [5, 6], [7, 8]]
```

&nbsp;[More Examples](https://github.com/openxla/stablehlo/tree/main/stablehlo/tests/interpret/concatenate.mlir)

-/

namespace SciLean


namespace Concatenate

structure Args {r k} (inDims : Fin k → Dims r) where
  dimension : Fin r

def Args.outShape {r k} {inDims : Fin k → Dims r} (args : Args inDims) : Dims r :=
  .ofFn fun d =>
    if d = args.dimension then
      ∑ i, (inDims i)[d]
    else if h : 0 < k then
      (inDims ⟨0, by linarith⟩)[d]
    else
      0

structure Preconditions {r k} {inDims : Fin k → Dims r} (args : Args inDims) : Prop where
  c1 : True
  c2 : ∀ d, d ≠ args.dimension → ∀ i j, (inDims i)[d] = (inDims j)[d]
  c3 : 0 < k
  c4 : (0:ℕ) ≤ args.dimension ∧ dimension < r
  c5 : True

structure Postconditions {r k} {inDims : Fin k → Dims r} (args : Args inDims) (outDims : Dims r) : Prop where
  c6 : ∀ d,
    if d = args.dimension then
      outDims[d] = ∑ i, (inDims i)[d]
    else
      ∀ i, outDims[d] = (inDims i)[d]

theorem postconditions_true {r k} {inDims : Fin k → Dims r} (args : Args inDims) (h : Preconditions args) :
    Postconditions args args.outShape := by
  constructor
  intro d; split_ifs; unfold Args.outShape; simp_all; unfold Args.outShape; intro i; simp_all; have := i.2; split_ifs; exact h.c2 d (by assumption) ⟨0,by omega⟩ i; have := i.2; simp_all

def Args.indexMap {r k} {inDims : Fin k → Dims r} (args : Args inDims)
  (h : Preconditions args)
  {outDims} (houtShape : outDims = args.outShape := by infer_var) :
  (i : Fin k) × TensorIndex (inDims i)
  ≃
  TensorIndex outDims := sorry


end Concatenate


open Concatenate in
def concatenate {r k} {inDims : Fin k → Dims r} {outDims : Dims r}
    (inputs : (i : Fin k) → TensorIndex (inDims i) → R)
    (args : Args inDims)
    (h : Preconditions args)
    (houtDims : outDims = args.outShape := by first | (try simp_all) | (try infer_var)) :
    TensorIndex outDims → R :=
  fun i =>
    let ⟨i,j⟩ := (args.indexMap h (by simp_all)).symm i
    inputs i j
