import SciLean.Modules.ML.XLA.TensorIndex
import SciLean.Modules.ML.XLA.Slice
import SciLean.Modules.ML.XLA.DotGeneral
import SciLean.Modules.ML.XLA.Pad
import SciLean.Modules.ML.XLA.Slice
import SciLean.Modules.ML.XLA.Concatenate
import SciLean.Modules.ML.XLA.Split

namespace SciLean

/-! StableHLO function: `convolution`

Spec: (source: https://github.com/openxla/stablehlo/blob/main/docs/spec.md)

### convolution

#### Semantics

Computes dot products between windows of `lhs` and slices of `rhs` and produces
`result`. The following diagram shows how elements in `result` are computed from
`lhs` and `rhs` using a concrete example.

![convolution](images/spec/convolution.svg)

More formally, consider the following reframing of the inputs in terms of `lhs`
in order to be able to express windows of `lhs`:

<!-- markdownlint-disable line-length -->
* `lhs_window_dimensions = lhs_shape(dim(lhs, input_batch_dimension), dim(rhs, kernel_spatial_dimensions), dim(lhs, input_feature_dimension))`.
* `lhs_window_strides = lhs_shape(1, window_strides, 1)`.
* `lhs_padding = lhs_shape([0, 0], padding, [0, 0])`.
* `lhs_base_dilations = lhs_shape(1, lhs_dilation, 1)`.
* `lhs_window_dilations = lhs_shape(1, rhs_dilation, 1)`.

This reframing uses the following helper functions:

* `lhs_shape(n, hw, c) = permute([n] + hw + [c], [input_batch_dimension] + input_spatial_dimensions + [input_feature_dimension])`.
* `result_shape(n1, hw, c1) = permute([n1] + hw + [c1], [output_batch_dimension] + output_spatial_dimensions + [output_feature_dimension])`.
* `permute([j0, j1, ..., jR-1], permutation) = [i0, i1, ..., iR-1]` where `j[d] = i[permutation[d]]`.

If `feature_group_count = 1` and `batch_group_count = 1`, then for all
`output_spatial_index` in `index_space(dim(result, output_spatial_dimensions...))`,
`result[result_shape(:, output_spatial_index, :)] = dot_product` where:

* `padding_value = constant(0, element_type(lhs))`.
* `padded_lhs = pad(lhs, padding_value, lhs_padding[:, 0], lhs_padding[:, 1], lhs_base_dilations - 1)`.
* `lhs_window_start = lhs_shape(0, output_spatial_index, 0) * lhs_window_strides`.
* `lhs_window = slice(padded_lhs, lhs_window_start, lhs_window_start + lhs_window_dimensions, lhs_window_dilations)`.
* `reversed_lhs_window = reverse(lhs_window, [input_spatial_dimensions[dim] for dim in range(size(window_reversal)) if window_reversal[dim] = true])`.
  This feature appears to be unused, so in the future we are planning to remove
  it ([#1181](https://github.com/openxla/stablehlo/issues/1181)).
* `dot_product = dot_general(reversed_lhs_window, rhs,
    lhs_batching_dimensions=[],
    lhs_contracting_dimensions=input_spatial_dimensions + [input_feature_dimension],
    rhs_batching_dimensions=[],
    rhs_contracting_dimensions=kernel_spatial_dimensions + [kernel_input_feature_dimension])`.

If `feature_group_count > 1`:

* `lhses = split(lhs, feature_group_count, input_feature_dimension)`.
* `rhses = split(rhs, feature_group_count, kernel_output_feature_dimension)`.
* `results... = convolution(lhses..., rhses..., ..., feature_group_count=1, ...)`.
* `result = concatenate(results, output_feature_dimension)`.

If `batch_group_count > 1`:

* `lhses = split(lhs, batch_group_count, input_batch_dimension)`.
* `rhses = split(rhs, batch_group_count, kernel_output_feature_dimension)`.
* `results... = convolution(lhses..., rhses..., ..., batch_group_count=1, ...)`.
* `result = concatenate(results, output_feature_dimension)`.
<!-- markdownlint-enable line-length -->

For quantized types, performs `dequantize_op_quantize(
    lambda lhs, rhs: convolution(lhs, rhs, window_strides, padding,
        lhs_dilation, rhs_dilation, window_reversal, input_batch_dimension,
        input_feature_dimension, input_spatial_dimensions,
        kernel_input_feature_dimension, kernel_output_feature_dimension,
        kernel_spatial_dimensions, output_batch_dimension,
        output_feature_dimension, output_spatial_dimensions,
        feature_group_count, batch_group_count, precision_config), lhs, rhs,
        type(result))`.

For hybrid quantized types, performs `hybrid_dequantize_then_op(
    lambda lhs, rhs: convolution(lhs, rhs, window_strides, padding,
        lhs_dilation, rhs_dilation, window_reversal, input_batch_dimension,
        input_feature_dimension, input_spatial_dimensions,
        kernel_input_feature_dimension, kernel_output_feature_dimension,
        kernel_spatial_dimensions, output_batch_dimension,
        output_feature_dimension, output_spatial_dimensions,
        feature_group_count, batch_group_count, precision_config), lhs, rhs)`.

#### Inputs

| Label | Name                              | Type                                                         | Constraints                                               |
|-------|-----------------------------------|--------------------------------------------------------------|-----------------------------------------------------------|
| (I1)  | `lhs`                             | tensor or per-tensor quantized tensor                        | (C1), (C10-C11), (C14) (C25), (C27-C28), (C31-C32), (C34) |
| (I2)  | `rhs`                             | tensor or quantized tensor                                   | (C1), (C14-C16), (C25), (C27-C29), (C31-C34)              |
| (I3)  | `window_strides`                  | 1-dimensional tensor constant of type `si64`                 | (C2-C3), (C25)                                            |
| (I4)  | `padding`                         | 2-dimensional tensor constant of type `si64`                 | (C4), (C25)                                               |
| (I5)  | `lhs_dilation`                    | 1-dimensional tensor constant of type `si64`                 | (C5-C6), (C25)                                            |
| (I6)  | `rhs_dilation`                    | 1-dimensional tensor constant of type `si64`                 | (C7-C8), (C25)                                            |
| (I7)  | `window_reversal`                 | 1-dimensional tensor constant of type `i1`                   | (C9)                                                      |
| (I8)  | `input_batch_dimension`           | constant of type `si64`                                      | (C10), (C13), (C25)                                       |
| (I9)  | `input_feature_dimension`         | constant of type `si64`                                      | (C11), (C13-C14)                                          |
| (I10) | `input_spatial_dimensions`        | 1-dimensional tensor constant of type `si64`                 | (C12), (C13), (C25)                                       |
| (I11) | `kernel_input_feature_dimension`  | constant of type `si64`                                      | (C14), (C18)                                              |
| (I12) | `kernel_output_feature_dimension` | constant of type `si64`                                      | (C15-C16), (C18), (C25), (C29)                            |
| (I13) | `kernel_spatial_dimensions`       | 1-dimensional tensor constant of type `si64`                 | (C17-C18), (C25)                                          |
| (I14) | `output_batch_dimension`          | constant of type `si64`                                      | (C20), (C25)                                              |
| (I15) | `output_feature_dimension`        | constant of type `si64`                                      | (C20), (C25), (C30)                                       |
| (I16) | `output_spatial_dimensions`       | 1-dimensional tensor constant of type `si64`                 | (C19-C20), (C25)                                          |
| (I17) | `feature_group_count`             | constant of type `si64`                                      | (C11), (C14), (C16), (C21), (C23)                         |
| (I18) | `batch_group_count`               | constant of type `si64`                                      | (C10), (C15), (C22), (C23), (C25)                         |
| (I19) | `precision_config`                | variadic number of enums of `DEFAULT`, `HIGH`, and `HIGHEST` | (C24)                                                     |

#### Outputs

| Name     | Type                       | Constraints                |
|----------|----------------------------|----------------------------|
| `result` | tensor or quantized tensor | (C25-C28), (C30), (C32-34) |

#### Constraints

<!-- markdownlint-disable line-length -->
* (C1) `N = rank(lhs) = rank(rhs)`.
* (C2) `size(window_strides) = N - 2`.
* (C3) `0 < window_strides`.
* (C4) `shape(padding) = [N - 2, 2]`.
* (C5) `size(lhs_dilation) = N - 2`.
* (C6) `0 < lhs_dilation`.
* (C7) `size(rhs_dilation) = N - 2`.
* (C8) `0 < rhs_dilation`.
* (C9) `size(window_reversal) = N - 2`.
* (C10) `dim(lhs, input_batch_dimension) % batch_group_count = 0`.
* (C11) `dim(lhs, input_feature_dimension) % feature_group_count = 0`.
* (C12) `size(input_spatial_dimensions) = N - 2`.
* (C13) Given `input_dimensions = [input_batch_dimension] +
       input_spatial_dimensions + [input_feature_dimension]`:
  * `is_unique(input_dimensions)`.
  * `0 <= input_dimensions < N`.
* (C14) `dim(rhs, kernel_input_feature_dimension) = dim(lhs, input_feature_dimension) / feature_group_count`.
* (C15) `dim(rhs, kernel_output_feature_dimension) % batch_group_count = 0`.
* (C16) `dim(rhs, kernel_output_feature_dimension) % feature_group_count = 0`.
* (C17) `size(kernel_spatial_dimensions) = N - 2`.
* (C18) Given `kernel_dimensions = kernel_spatial_dimensions +
        [kernel_input_feature_dimension] + [kernel_output_feature_dimension]`:
  * `is_unique(kernel_dimensions)`.
  * `0 <= kernel_dimensions < N`.
* (C19) `size(output_spatial_dimensions) = N - 2`.
* (C20) Given `output_dimensions = [output_batch_dimension] +
        output_spatial_dimensions + [output_feature_dimension]`:
  * `is_unique(output_dimensions)`.
  * `0 <= output_dimensions < N`.
* (C21) `0 < feature_group_count`.
* (C22) `0 < batch_group_count`.
* (C23) `feature_group_count = 1 or batch_group_count = 1`.
* (C24) `size(precision_config) = 2`.
* (C25) `dim(result, result_dim)` is defined as:
  * `dim(lhs, input_batch_dimension) / batch_group_count` if `result_dim = output_batch_dimension`.
  * `dim(rhs, kernel_output_feature_dimension)` if `result_dim = output_feature_dimension`.
  * `num_windows` otherwise, where:
    * `output_spatial_dimensions[spatial_dim] = result_dim`.
    * `lhs_dim = input_spatial_dimensions[spatial_dim]`.
    * `rhs_dim = kernel_spatial_dimensions[spatial_dim]`.
    * `dilated_input_shape[lhs_dim] = dim(lhs, lhs_dim) = 0 ? 0 : (dim(lhs, lhs_dim) - 1) * lhs_dilation[spatial_dim] + 1`.
    * `padded_input_shape[lhs_dim] = padding[spatial_dim, 0] + dilated_input_shape[lhs_dim] + padding[spatial_dim, 1]`.
    * `dilated_window_shape[lhs_dim] = dim(rhs, rhs_dim) = 0 ? 0 : (dim(rhs, rhs_dim) - 1) * rhs_dilation[spatial_dim] + 1`.
    * `is_empty_window[lhs_dim] = padded_input_shape[lhs_dim] = 0 || dilated_window_shape[lhs_dim] > padded_input_shape[lhs_dim]`.
    * `num_windows = is_empty_window[lhs_dim] ? 0 : floor((padded_input_shape[lhs_dim] - dilated_window_shape[lhs_dim]) / window_strides[spatial_dim]) + 1`.
* (C26) `rank(result) = N`.
* If the operation uses non-quantized tensors:
  * (C27) `element_type(lhs) = element_type(rhs) = element_type(result)`.
* If the operation uses quantized tensors:
  * (C28) `is_quantized(lhs) = is_quantized(result) and is_quantized(rhs)`.
  * (C29) If `is_per_axis_quantized(rhs)`,
    then `quantization_dimension(rhs) = kernel_output_feature_dimension`.
  * (C30) If `is_per_axis_quantized(result)`, then
    `quantization_dimension(result) = output_feature_dimension`.
  * If `is_quantized(lhs)`:
    * (C31) `storage_type(lhs) = storage_type(rhs)`.
    * (C32) `expressed_type(lhs) = expressed_type(rhs) = expressed_type(result)`.
    * (C33) If `is_per_tensor_quantized(rhs)`, then
      `is_per_tensor_quantized(result)`.
  * If `!is_quantized(lhs)`:
    * (C34) `element_type(lhs) = expressed_type(rhs) = element_type(result)`.
<!-- markdownlint-enable line-length -->

#### Examples

```mlir
// %lhs: [[
//        [
//          [1], [2], [5], [6]
//        ],
//        [
//          [3], [4], [7], [8]
//        ],
//        [
//          [10], [11], [14], [15]
//        ],
//        [
//          [12], [13], [16], [17]
//        ]
//      ]]
//
// %rhs: [
//        [[[1]], [[1]], [[1]]],
//        [[[1]], [[1]], [[1]]],
//        [[[1]], [[1]], [[1]]]
//       ]
%result = "stablehlo.convolution"(%lhs, %rhs) {
  window_strides = array<i64: 4, 4>,
  padding = dense<0> : tensor<2x2xi64>,
  lhs_dilation = array<i64: 2, 2>,
  rhs_dilation = array<i64: 1, 1>,
  window_reversal = array<i1: false, false>,
  // In the StableHLO dialect, dimension numbers are encoded via:
  // `[<input dimensions>]x[<kernel dimensions>]->[output dimensions]`.
  // "b" is batch dimension, "f" is feature dimension,
  // "i" is input feature dimension, "o" is output feature dimension,
  // "0/1/etc" are spatial dimensions.
  dimension_numbers = #stablehlo.conv<[b, 0, 1, f]x[0, 1, i, o]->[b, 0, 1, f]>,
  batch_group_count = 1 : i64,
  feature_group_count = 1 : i64,
  precision_config = [#stablehlo<precision DEFAULT>, #stablehlo<precision DEFAULT>]
} : (tensor<1x4x4x1xi64>, tensor<3x3x1x1xi64>) -> tensor<1x2x2x1xi64>
// %result: [[
//            [[10], [26]],
//            [[46], [62]]
//          ]]
```

&nbsp;[More Examples](../stablehlo/tests/interpret/convolution.mlir)

-/

namespace Convolution

structure Args {r} (lhsDims rhsDims : Dims r) where
  window_strides : ArrayN ℤ (r-2)
  padding : ArrayN (ℤ×ℤ) (r-2)
  lhs_dilation : ArrayN ℕ+ (r-2)
  rhs_dilation : ArrayN ℕ+ (r-2)
  window_reversal : ArrayN Bool r
  input_batch_dimension : Fin r
  input_feature_dimension : Fin r
  input_spatial_dimensions : ArrayN (Fin r) (r-2)
  kernel_input_feature_dimension : Fin r
  kernel_output_feature_dimension : Fin r
  kernel_spatial_dimensions : ArrayN (Fin r) (r-2)
  output_batch_dimension : Fin r
  output_feature_dimension : Fin r
  output_spatial_dimensions : ArrayN (Fin r) (r-2)
  feature_group_count : ℕ+
  batch_group_count : ℕ+
  precision_config : True

namespace Args

  def lhsSpatialShape {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) : Dims (r - 2) := sorry

  def rhsSpatialShape {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) : Dims (r - 2) := sorry

  def outSpatialShape {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) : Dims (r - 2) := sorry

  def lowPadding {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) : ArrayN ℤ (r-2) := args.padding.map (·.1)

  def highPadding {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) : ArrayN ℤ (r-2) := args.padding.map (·.2)

  def lhsShapeMap {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) :
    α × ArrayN α (r - 2) × α
    ≃
    ArrayN α r := sorry

  def rhsShapeMap {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) :
    α × ArrayN α (r - 2) × α
    ≃
    ArrayN α r := sorry

  def outShapeMap {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) :
    α × ArrayN α (r - 2) × α
    ≃
    ArrayN α r := sorry

  def outDims {r} {lhsDims rhsDims : Dims r}
      (args : Args lhsDims rhsDims) : Dims r :=

    let output_batch_dim_size := lhsDims[args.input_batch_dimension] / args.batch_group_count
    let output_feature_dim_size := rhsDims[args.kernel_output_feature_dimension]

    let dilated_input_shape := (args.lhsSpatialShape - 1) * args.lhs_dilation + 1
    let padded_input_shape := args.lowPadding + dilated_input_shape + args.highPadding
    let dilated_window_shape := (args.rhsSpatialShape - 1) * args.rhs_dilation + 1
    let is_empty_window := padded_input_shape ≤ 0 || dilated_window_shape > padded_input_shape
    let output_spatial_dims := if is_empty_window then 0 else (padded_input_shape - dilated_window_shape) / args.window_strides + 1

    args.outShapeMap (output_batch_dim_size, output_spatial_dims, output_feature_dim_size)

end Args

structure Conditions {r} {lhsDims rhsDims : Dims r}
    (args : Args lhsDims rhsDims) (outDims : Dims r) where
  c1 : lhsDims = rhsDims
  c2 : args.window_strides.size = r - 2
  c3 : 0 < args.window_strides
  c4 : args.padding.size = r - 2
  c5 : args.lhs_dilation.size = r - 2
  c6 : 0 < args.lhs_dilation.toNat
  c7 : args.rhs_dilation.size = r - 2
  c8 : 0 < args.rhs_dilation.toNat
  c9 : args.window_reversal.size = r
  c10 : lhsDims[args.input_batch_dimension] % args.batch_group_count = 0
  c11 : lhsDims[args.input_feature_dimension] % args.feature_group_count = 0
  c12 : args.input_spatial_dimensions.size = r - 2
  c13 : ∀ d, (0:ℕ) ≤ args.input_spatial_dimensions[d] ∧ args.input_spatial_dimensions[d] < r
  c14 : rhsDims[args.kernel_input_feature_dimension] = lhsDims[args.input_feature_dimension] / args.feature_group_count
  c15 : rhsDims[args.kernel_output_feature_dimension] % args.batch_group_count = 0


end Convolution

variable {R} [RealScalar R]

-- case
open Convolution in
def convolutionCore {r} {lhsDims rhsDims outDims : Dims r}
    (lhs : TensorIndex lhsDims → R) (rhs : TensorIndex rhsDims → R)
    (args : Args lhsDims rhsDims)
    (h : Conditions args outDims) :
    TensorIndex outDims → R :=

  fun i =>
    let (_,output_spatial_index,_) := args.outShapeMap.symm i.1 -- get the correct parts of `i`

    let lhsWindowShape :=
      args.lhsShapeMap (lhsDims[args.input_batch_dimension],
                        args.rhsSpatialShape,
                        lhsDims[args.input_feature_dimension])
    let lhs_window_strides := args.lhsShapeMap (1,args.window_strides,1)
    let lhs_padding_low  := args.lhsShapeMap (0,args.lowPadding,0)
    let lhs_padding_high := args.lhsShapeMap (0,args.highPadding,0)
    let lhs_base_dilation := args.lhsShapeMap (1,args.lhs_dilation,1)
    let lhs_window_dilations := args.lhsShapeMap (1,args.rhs_dilation,1)

    let padArgs : Pad.Args lhsDims := {
      edge_padding_low := lhs_padding_low
      edge_padding_high := lhs_padding_high
      interior_padding := lhs_base_dilation.toNat
    }
    let padded_lhs := pad lhs 0 padArgs
      -- there is some issue with elaboration and we have to specify these arguments explicitly
      (outDims:= padArgs.outShape) (by infer_var)


    let lhs_window_start : ArrayN ℤ r := args.lhsShapeMap (0,output_spatial_index,0)
    let sliceArgs : Slice.Args padArgs.outShape := {
      start_indices := lhs_window_start
      limit_indices := (lhs_window_start + lhsWindowShape)
      strides := lhs_window_dilations
    }
    let lhs_window := slice padded_lhs sliceArgs sorry
      -- there is some issue with elaboration and we have to specify these arguments explicitly
      (outDims:=sliceArgs.outShape) (by infer_var)

    let dotArgs : DotGeneral.Args sliceArgs.outShape rhsDims :=
        {lhs_batching_dimensions := #[]
         rhs_batching_dimensions := #[]
         lhs_contracting_dimensions := args.input_spatial_dimensions.1 ++ #[args.input_feature_dimension]
         rhs_contracting_dimensions := args.kernel_spatial_dimensions.1 ++ #[args.kernel_input_feature_dimension]}

    let dot_product : R :=
      dot_general lhs_window rhs dotArgs
        (t := 0) (outDims := ⟨#[],by simp⟩) (by sorry) (by sorry) ⟨⟨#[],by simp⟩,by simp⟩

    dot_product


#check Array.modify

open Convolution in
def convolution {r} {lhsDims rhsDims outDims : Dims r}
    (lhs : TensorIndex lhsDims → R) (rhs : TensorIndex rhsDims → R)
    (args : Args lhsDims rhsDims)
    (h : Conditions args outDims) : TensorIndex outDims → R :=

  if args.feature_group_count > 1 then
    let lhsDims' : Dims r := ⟨lhsDims.1.modify args.input_feature_dimension.1 (fun d => d / args.feature_group_count), sorry⟩
    let lhses : Fin args.feature_group_count → TensorIndex lhsDims' → R := sorry
       --split lhs args.feature_group_count args.input_feature_dimension
    let rhsDims' : Dims r := ⟨rhsDims.1.modify args.kernel_output_feature_dimension.1 (fun d => d / args.feature_group_count), sorry⟩
    let rhsSplitArgs : Split.Args rhsDims := {
      split_size := args.feature_group_count
      split_dimension := args.kernel_output_feature_dimension
    }
    let rhses := split rhs rhsSplitArgs sorry (outDims := rhsSplitArgs.outShape) (by simp)
       --split rhs args.feature_group_count args.kernel_output_feature_dimension
    let results := fun i => convolution (lhses i) (rhses i) args h
    concatenate results args.output_feature_dimension
  else if args.batch_group_count > 1 then
    let lhses := split lhs args.batch_group_count args.input_batch_dimension
    let rhses := split rhs args.batch_group_count args.kernel_output_feature_dimension
    let results := lhses.zipWith rhses (fun lhs rhs => convolutionCore lhs rhs args h)
    concatenate results args.output_feature_dimension
  else
    convolutionCore lhs rhs args h
