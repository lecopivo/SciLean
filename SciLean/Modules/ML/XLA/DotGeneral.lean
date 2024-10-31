import SciLean.Modules.ML.XLA.TensorIndex
import SciLean.Modules.ML.XLA.ConvWithPadding

namespace SciLean

/-! StableHLO function: `dot_general`

Spec: (source: https://github.com/openxla/stablehlo/blob/main/docs/spec.md)

### dot_general

#### Semantics

Computes dot products between slices of `lhs` and slices of `rhs` and produces a
`result` tensor.

More formally, `result[result_index] = dot_product`, where:

<!-- markdownlint-disable line-length -->
* `lhs_result_dimensions = [d for d in axes(lhs) and d not in lhs_batching_dimensions and d not in lhs_contracting_dimensions]`.
* `rhs_result_dimensions = [d for d in axes(rhs) and d not in rhs_batching_dimensions and d not in rhs_contracting_dimensions]`.
* `result_batching_index + result_lhs_index + result_rhs_index = result_index`
  where `size(result_batching_index) = size(lhs_batching_dimensions)`,
  `size(result_lhs_index) = size(lhs_result_dimensions)` and
  `size(result_rhs_index) = size(rhs_result_dimensions)`.
* `transposed_lhs = transpose(lhs, lhs_batching_dimensions + lhs_result_dimensions + lhs_contracting_dimensions)`.
* `transposed_lhs_slice = slice(transposed_lhs, result_batching_index + result_lhs_index + [:, ..., :])`.
* `reshaped_lhs_slice = reshape(transposed_lhs_slice, dims(lhs, lhs_contracting_dimensions))`.
* `transposed_rhs = transpose(rhs, rhs_batching_dimensions + rhs_result_dimensions + rhs_contracting_dimensions)`.
* `transposed_rhs_slice = slice(transposed_rhs, result_batching_index + result_rhs_index + [:, ..., :])`.
* `reshaped_rhs_slice = reshape(transposed_rhs_slice, dims(rhs, rhs_contracting_dimensions))`.
* `dot_product = reduce(
    inputs=[multiply(reshaped_lhs_slice, reshaped_rhs_slice)],
    init_values=[constant(0, element_type(result))],
    dimensions=range(size(lhs_contracting_dimensions)),
    body=lambda x, y: add(x, y))`.
<!-- markdownlint-enable line-length -->

For quantized types, performs `dequantize_op_quantize(
    lambda lhs, rhs: dot_general(lhs, rhs, lhs_batching_dimensions,
        rhs_batching_dimensions, lhs_contracting_dimensions,
        rhs_contracting_dimensions, precision_config), lhs, rhs, type(result))`.

For hybrid quantized types, performs `hybrid_dequantize_then_op(
    lambda lhs, rhs: dot_general(lhs, rhs, lhs_batching_dimensions,
        rhs_batching_dimensions, lhs_contracting_dimensions,
        rhs_contracting_dimensions, precision_config), lhs, rhs)`.

`precision_config` controls the tradeoff between speed and accuracy for
computations on accelerator backends. This can be one of the following (at the
moment, the semantics of these enum values is underspecified, but we are
planning to address this in
[#755](https://github.com/openxla/stablehlo/issues/755)):

* `DEFAULT`: Fastest calculation, but least accurate approximation to the
  original number.
* `HIGH`: Slower calculation, but more accurate approximation to the
  original number.
* `HIGHEST`: Slowest calculation, but most accurate approximation to the
  original number.

A `DotAlgorithm` defines the main properties of the algorithm used to implement
the dot operation, which also defines the precision. If the algorithm attribute
fields are set, then the `precision_config` must be `DEFAULT`. `DotAlgorithms`
do not have a default value, as the default parameters are implementation
defined. As such, all dot algorithm fields may be set to `None` to specify an
empty dot algorithm, which will instead use the `precision_config` value.

`DotAlgorithm` fields include:

* `lhs_precision_type` and `rhs_precision_type`, the precisions that the LHS and
  RHS of the operation are rounded to. Precision types are independent from the
  storage types of the inputs and the output.
* `accumulation_type` the precision used for accumulation.
* `lhs_component_count`, `rhs_component_count`, and `num_primitive_operations`
  apply when we are doing an algorithm which decomposes the LHS and/or RHS into
  multiple components and does multiple "primitive" dot operations on those
  values - usually to emulate a higher precision (e.g.
[Leveraging the bfloat16 Artificial Intelligence Datatype For Higher-Precision Computations](https://arxiv.org/pdf/1904.06376.pdf):
  bf16_6x tf32_3x, etc). For algorithms with no decomposition, these values
  should be set to `1`.
* `allow_imprecise_accumulation` to specify if accumulation in lower precision
  is permitted for some steps (e.g. `CUBLASLT_MATMUL_DESC_FAST_ACCUM`).

Example `DotAlgorithm` attributes:

```txt
// Inputs are casted to tf32, and then accumulated in f32:
{lhs_precision_type = tf32,
 rhs_precision_type = tf32,
 accumulation_type = f32,
 lhs_component_count = 1,
 rhs_component_count = 1,
 num_primitive_operations = 1,
 allow_imprecise_accumulation = false}


// bf16_6x: each input is decomposed to 3 bf16 components, then 6 dot operations are done on those components, and the result is accumulated in f32.
{lhs_precision_type = bf16,
 rhs_precision_type = bf16,
 accumulation_type = f32,
 lhs_component_count = 3,
 rhs_component_count = 3,
 num_primitive_operations = 6,
 allow_imprecise_accumulation = false}


// Inputs are (casted to) f8e5m2, and we accumulate in f32, but for some steps we may accumulate in lower precision.
{lhs_precision_type = f8e5m2,
 rhs_precision_type = f8e5m2,
 accumulation_type = f32,
 lhs_component_count = 1,
 rhs_component_count = 1,
 num_primitive_operations = 1,
 allow_imprecise_accumulation = true}
```

It is up to the implementations to decide which combinations are supported. In
general, it is not guaranteed that each algorithm is supported on each
accelerator type by the consumer of the StableHLO. If a given algorithm is not
supported, an error should be raised as opposed to falling back to an
alternative. StableHLO verification will provide best effort verification,
preventing algorithms that are not known to be supported on *any* hardware.

See [`xla_data.proto > Algorithm`](https://github.com/openxla/xla/blob/e8a707554de6b3d6bfd891583a81ff7020a97b54/xla/xla_data.proto#L1022)
for some supported algorithm values. Ticket #2483 captures the plan to create a
centralized doc on supported algorithms by backend.

#### Inputs

| Label | Name                           | Type                                                         | Constraints                                    |
|-------|--------------------------------|--------------------------------------------------------------|------------------------------------------------|
| (I1)  | `lhs`                          | tensor or per-tensor quantized tensor                        | (C5-C6), (C9-C10), (C12-C14), (C17-C18), (C20) |
| (I2)  | `rhs`                          | tensor or quantized tensor                                   | (C7-C10), (C12-C20)                            |
| (I3)  | `lhs_batching_dimensions`      | 1-dimensional tensor constant of type `si64`                 | (C1), (C3), (C5), (C9), (C12)                  |
| (I4)  | `rhs_batching_dimensions`      | 1-dimensional tensor constant of type `si64`                 | (C1), (C4), (C7), (C9)                         |
| (I5)  | `lhs_contracting_dimensions`   | 1-dimensional tensor constant of type `si64`                 | (C2), (C3), (C6), (C10)                        |
| (I6)  | `rhs_contracting_dimensions`   | 1-dimensional tensor constant of type `si64`                 | (C2), (C4), (C8), (C10), (C16)                 |
| (I7)  | `precision_config`             | variadic number of enums of `DEFAULT`, `HIGH`, and `HIGHEST` | (C11), (C21)                                   |
| (I8)  | `lhs_precision_type`           | FloatType or TensorFloat32                                   | (C21)                                          |
| (I9)  | `rhs_precision_type`           | FloatType or TensorFloat32                                   | (C21)                                          |
| (I10) | `accumulation_type`            | FloatType or TensorFloat32                                   | (C21)                                          |
| (I11) | `lhs_component_count`          | constant of type `si32`                                      | (C21), (C22)                                   |
| (I12) | `rhs_component_count`          | constant of type `si32`                                      | (C21), (C23)                                   |
| (I13) | `num_primitive_operations`     | constant of type `si32`                                      | (C21), (C24)                                   |
| (I14) | `allow_imprecise_accumulation` | constant of type `bool`                                      | (C21)                                          |

#### Outputs

| Name     | Type                       | Constraints             |
|----------|----------------------------|-------------------------|
| `result` | tensor or quantized tensor | (C12), (C14), (C18-C20) |

#### Constraints

* (C1) `size(lhs_batching_dimensions) = size(rhs_batching_dimensions)`.
* (C2) `size(lhs_contracting_dimensions) =
  size(rhs_contracting_dimensions)`.
* (C3) `is_unique(lhs_batching_dimensions + lhs_contracting_dimensions)`.
* (C4) `is_unique(rhs_batching_dimensions + rhs_contracting_dimensions)`.
* (C5) `0 <= lhs_batching_dimensions < rank(lhs)`.
* (C6) `0 <= lhs_contracting_dimensions < rank(lhs)`.
* (C7) `0 <= rhs_batching_dimensions < rank(rhs)`.
* (C8) `0 <= rhs_contracting_dimensions < rank(rhs)`.
* (C9) `dim(lhs, lhs_batching_dimensions...) =
  dim(rhs, rhs_batching_dimensions...)`.
* (C10) `dim(lhs, lhs_contracting_dimensions...) =
  dim(rhs, rhs_contracting_dimensions...)`.
* (C11) `size(precision_config) = 2`.
* (C12) `shape(result) = dim(lhs, lhs_batching_dimensions) +
  dim(lhs, lhs_result_dimensions) + dim(rhs, rhs_result_dimensions)`.
* If the operation uses non-quantized tensors:
  * (C13) `element_type(lhs) = element_type(rhs)`.
* If the operation uses quantized tensors:
  * (C14) `is_quantized(lhs) = is_quantized(result) and is_quantized(rhs)`.
  * (C15) `zero_points(rhs) = 0`.
  * (C16) If `is_per_axis_quantized(rhs)`, then
    `quantization_dimension(rhs)` not in `rhs_contracting_dimensions`.
  * If `is_quantized(lhs)`:
    * (C17) `storage_type(lhs) = storage_type(rhs)`.
    * (C18) `expressed_type(lhs) = expressed_type(rhs) = expressed_type(result)`.
    * (C19) If `is_per_tensor_quantized(rhs)`, then
      `is_per_tensor_quantized(result)`.
  * If `!is_quantized(lhs)`:
    * (C20) `element_type(lhs) = expressed_type(rhs) = element_type(result)`.
* If `!is_empty_algorithm(lhs_precision_type, rhs_precision_type,
  accumulation_type, lhs_component_count, rhs_component_count,
  num_primitive_operations allow_imprecise_accumulation)`:
  * (C21) `precision_config... = DEFAULT`.
  * (C22) `0 < lhs_component_count`.
  * (C23) `0 < rhs_component_count`.
  * (C24) `0 < num_primitive_operations`.

#### Examples

```mlir
// %lhs: [
//        [[1, 2],
//         [3, 4]],
//        [[5, 6],
//         [7, 8]]
//       ]
// %rhs: [
//        [[1, 0],
//         [0, 1]],
//        [[1, 0],
//         [0, 1]]
//       ]
%result = "stablehlo.dot_general"(%lhs, %rhs) {
  dot_dimension_numbers = #stablehlo.dot<
    lhs_batching_dimensions = [0],
    rhs_batching_dimensions = [0],
    lhs_contracting_dimensions = [2],
    rhs_contracting_dimensions = [1]
  >,
  precision_config = [#stablehlo<precision DEFAULT>, #stablehlo<precision DEFAULT>],
  algorithm = #stablehlo.dot_algorithm<
    lhs_precision_type = tf32,
    rhs_precision_type = tf32,
    accumulation_type = f32,
    lhs_component_count = 1,
    rhs_component_count = 1,
    num_primitive_operations = 1,
    allow_imprecise_accumulation = false
  >
} : (tensor<2x2x2xi64>, tensor<2x2x2xi64>) -> tensor<2x2x2xi64>
// %result: [
//           [[1, 2],
//            [3, 4]],
//           [[5, 6],
//            [7, 8]]
//          ]
```

&nbsp;[More Examples](https://github.com/openxla/stablehlo/tree/main/stablehlo/tests/interpret/dot_general.mlir)


-/

variable {R} [RealScalar R]

namespace DotGeneral

structure Args {r s} (lhsDims : Dims r) (rhsDims : Dims s) where
  lhs_batching_dimensions : Array (Fin r)
  rhs_batching_dimensions : Array (Fin s)
  lhs_contracting_dimensions : Array (Fin r)
  rhs_contracting_dimensions : Array (Fin s)


def Args.outShape' {r s} {lhsDims : Dims r} {rhsDims : Dims s} (args : Args lhsDims rhsDims) : Array ℤ :=
  let lhs_all_dims := List.ofFn (fun i : Fin r => i)
  let lhs_result_dimensions : Array (Fin r) :=
    lhs_all_dims.diff (args.lhs_batching_dimensions ++ args.lhs_contracting_dimensions).toList |>.toArray

  let rhs_all_dims := List.ofFn (fun i : Fin s => i)
  let rhs_result_dimensions : Array (Fin s) :=
    rhs_all_dims.diff (args.rhs_batching_dimensions ++ args.rhs_contracting_dimensions).toList |>.toArray

  let outShape :=
    args.lhs_batching_dimensions.map (lhsDims[·])
    ++
    lhs_result_dimensions.map (lhsDims[·])
    ++
    rhs_result_dimensions.map (rhsDims[·])

  outShape

def Args.outRank {r s} {lhsDims : Dims r} {rhsDims : Dims s} (args : Args lhsDims rhsDims) : ℕ :=
    args.outShape'.size

def Args.outShape {r s} {lhsDims : Dims r} {rhsDims : Dims s} (args : Args lhsDims rhsDims)
    {t} (h : t = args.outRank := by (try simp_all); (try infer_var)) : Dims t :=
  ⟨args.outShape', by simp_all[Args.outRank]⟩

structure Preconditions {r s t} {lhsDims : Dims r} {rhsDims : Dims s} (args : Args lhsDims rhsDims) (outDims : Dims t) where
  c1 : args.lhs_batching_dimensions.size = args.rhs_batching_dimensions.size
  c2 : args.lhs_contracting_dimensions.size = args.rhs_contracting_dimensions.size
  c3 : (args.lhs_batching_dimensions ++ args.lhs_contracting_dimensions).toList.Nodup
  c4 : (args.rhs_batching_dimensions ++ args.rhs_contracting_dimensions).toList.Nodup
  c5 : args.lhs_batching_dimensions.all (fun i => i.val < r)
  c6 : args.lhs_contracting_dimensions.all (fun i => i.val < r)
  c7 : args.rhs_batching_dimensions.all (fun i => i.val < s)
  c8 : args.rhs_contracting_dimensions.all (fun i => i.val < s)
  c9 : args.lhs_batching_dimensions.map (lhsDims[·]) = args.rhs_batching_dimensions.map (rhsDims[·])
  c10 : args.lhs_contracting_dimensions.map (lhsDims[·]) = args.rhs_contracting_dimensions.map (rhsDims[·])
  c11 : True
  c12 :
    let lhs_result_dimensions : Array (Fin r) :=
      (Array.ofFn (fun i : Fin r => i)).filter (fun d => ¬args.lhs_batching_dimensions.contains d ∧ ¬args.lhs_contracting_dimensions.contains d)
    let rhs_result_dimensions : Array (Fin s) :=
      (Array.ofFn (fun i : Fin s => i)).filter (fun d => ¬args.rhs_batching_dimensions.contains d ∧ ¬args.rhs_contracting_dimensions.contains d)
    let outShape :=
      args.lhs_batching_dimensions.map (lhsDims[·])
      ++
      lhs_result_dimensions.map (lhsDims[·])
      ++
      rhs_result_dimensions.map (rhsDims[·])
    outDims.1 = outShape

structure Postcondition {r s t} {lhsDims : Dims r} {rhsDims : Dims s} (args : Args lhsDims rhsDims) (outDims : Dims t) where
  c12' : t = args.outRank
  c12  : outDims = args.outShape (by simp_all)


def Args.batchDims {r s} {lhsDims : Dims r} {rhsDims : Dims s}
    (args : Args lhsDims rhsDims)
    {n} (h : n = args.lhs_batching_dimensions.size := by infer_var) : Dims n :=
  ⟨args.lhs_batching_dimensions.map (lhsDims[·]), by simp_all⟩

def Args.contraDims {r s} {lhsDims : Dims r} {rhsDims : Dims s}
    (args : Args lhsDims rhsDims)
    {n} (h : n = args.lhs_contracting_dimensions.size := by infer_var) : Dims n :=
  ⟨args.lhs_contracting_dimensions.map (lhsDims[·]), by simp_all⟩


def Args.lhsResultDims {r s} {lhsDims : Dims r} {rhsDims : Dims s}
    (args : Args lhsDims rhsDims)
    {n} (h : n = r - args.lhs_batching_dimensions.size - args.lhs_contracting_dimensions.size := by infer_var) : Dims n :=
  ⟨(Array.ofFn (fun i : Fin r => i))
    |>.filter (fun d => (d ∉ args.lhs_batching_dimensions) ∧ (d ∉ args.lhs_contracting_dimensions))
    |>.map (fun i => i.1),
   by sorry /- this proof depends on `args.c3` ! -/⟩


def Args.rhsResultDims {r s} {lhsDims : Dims r} {rhsDims : Dims s}
    (args : Args lhsDims rhsDims)
    {n} (h : n = r - args.rhs_batching_dimensions.size - args.rhs_contracting_dimensions.size := by infer_var) : Dims n :=
  ⟨(Array.ofFn (fun i : Fin s => i))
    |>.filter (fun d => (d ∉ args.rhs_batching_dimensions) ∧ (d ∉ args.rhs_contracting_dimensions))
    |>.map (fun i => i.1),
   by sorry /- this proof depends on `args.c4` ! -/⟩


def Args.lhsIndexMap {r s} {lhsDims : Dims r} {rhsDims : Dims s}
    (args : Args lhsDims rhsDims) :
    TensorIndex lhsDims
    ≃
    TensorIndex args.batchDims × TensorIndex args.contraDims × TensorIndex args.lhsResultDims where
  toFun := fun i => sorry
  invFun := fun ⟨i,l,j⟩ => sorry
  left_inv := sorry
  right_inv := sorry


def Args.rhsIndexMap {r s} {lhsDims : Dims r} {rhsDims : Dims s}
  (args : Args lhsDims rhsDims) :
  TensorIndex rhsDims
  ≃
  TensorIndex args.batchDims × TensorIndex args.contraDims × TensorIndex args.rhsResultDims := sorry


def Args.outIndexMap {r s t} {lhsDims : Dims r} {rhsDims : Dims s} {outDims : Dims t}
  (args : Args lhsDims rhsDims)
  (h : t = args.outRank := by infer_var)
  (houtDims : outDims = args.outShape := by infer_var) :
  TensorIndex outDims
  ≃
  TensorIndex args.batchDims × TensorIndex args.lhsResultDims × TensorIndex args.rhsResultDims := sorry


end DotGeneral


open DotGeneral in
def dot_general {r s t} {lhsDims : Dims r} {rhsDims : Dims s} {outDims : Dims t}
    (lhs : TensorIndex lhsDims → R)
    (rhs : TensorIndex rhsDims → R)
    (args : Args lhsDims rhsDims)
    (ht : t = args.outRank := by infer_var)
    (houtDims : outDims = args.outShape := by infer_var) :
    TensorIndex outDims → R :=
  fun i =>
    let (i,j,k) := args.outIndexMap (by simp_all) (by simp_all) i
    ∑ l : TensorIndex args.contraDims,
      lhs (args.lhsIndexMap.symm (i,l,j)) * rhs (args.rhsIndexMap.symm (i,l,k))
