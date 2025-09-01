import SciLean.Modules.ML.XLA.ConvWithPaddingStride
import SciLean.Modules.ML.XLA.Pad
import SciLean.Modules.ML.XLA.DotGeneral
import SciLean.Modules.ML.XLA.Slice
import Mathlib.Tactic.SplitIfs

namespace SciLean

variable {R} [RealScalar R] [PlainDataType R]

open Set in
instance (a b : ℤ) : IndexType (Ico a b) := sorry
#synth Coe ℕ+ ℕ

open Set in
def convolutionB {lhsDims rhsDims : Dims (r+2)}
   (lhs : TensorIndex lhsDims → R) (rhs : TensorIndex rhsDims → R)
   (lhsDimMap rhsDimMap outDimMap : DimMap r)
   (low high : ArrayN ℤ r)    -- padding
   (stride : ArrayN ℕ+ r)    -- window stride
   (xdil ydil : ArrayN ℕ+ r) -- dillatation
   (feature_group_count batch_group_count : ℕ+)
   (outDims : Dims (r+2)) : TensorIndex outDims → R :=

  let lhsSpDims := lhsDimMap.spatialDims lhsDims
  let lhsBatchDim := lhsDimMap.batchDim lhsDims
  let lhsFeatureDim := lhsDimMap.featureDim lhsDims
  let lhsIndexMap := lhsDimMap.indexMap lhsDims (by infer_var) (by infer_var) (by infer_var)

  let rhsSpDims := rhsDimMap.spatialDims rhsDims
  let rhsBatchDim := rhsDimMap.batchDim rhsDims
  let rhsFeatureDim := rhsDimMap.featureDim rhsDims
  let rhsIndexMap := rhsDimMap.indexMap rhsDims (by infer_var) (by infer_var) (by infer_var)

  let outSpDims := outDimMap.spatialDims outDims
  let outBatchDim := outDimMap.batchDim outDims
  let outFeatureDim := outDimMap.featureDim outDims
  let outIndexMap := outDimMap.indexMap outDims (by infer_var) (by infer_var) (by infer_var)

  have houtDim : outSpDims = convOutDim lhsSpDims rhsSpDims low high stride xdil ydil := sorry

  -- have c10 : lhsBatchDim % batch_group_count = 0 := sorry
  -- have c11 : lhsFeatureDim % feature_group_count = 0 := sorry

  -- have c14 : rhsBatchDim = lhsFeatureDim / feature_group_count := sorry
  -- have c15 : rhsFeatureDim % batch_group_count = 0 := sorry
  -- have c16 : rhsFeatureDim % feature_group_count = 0 := sorry

  -- have c23 : feature_group_count = 1 ∨ batch_group_count = 1 := sorry

  -- have c25_1 : outBatchDim = lhsBatchDim / batch_group_count := sorry
  -- have c25_2 : outFeatureDim = rhsFeatureDim / batch_group_count := sorry


  fun (i : TensorIndex outDims) =>
    let i := outIndexMap.toFun i
    let bi := i.1; let fi := i.2.1; let si := i.2.2

    ∑ (bg : Fin batch_group_count),
    ∑ (fg : Fin feature_group_count),

    ∑ (fj : Ico 0 rhsFeatureDim),
    ∑ (bj : Ico 0 rhsBatchDim),

    let bk : Ico 0 lhsBatchDim := ⟨bi * bg, by sorry⟩ -- c25.1
    let fk : Ico 0 lhsFeatureDim := ⟨fg * fj, by sorry⟩ -- c25.2

    let fi : Ico 0 outFeatureDim := ⟨bj.1 * fg, by sorry⟩

      -- fi = bj * fg

      -- however one of `bg` or `fg` is one
      -- fj = bg * x
      -- fj = fg * y

    let lhs' := fun (sk : TensorIndex lhsSpDims) => lhs (lhsIndexMap.symm (bk,fk,sk))
    let rhs' := fun (sj : TensorIndex rhsSpDims) => rhs (rhsIndexMap.symm (bj,fj,sj))

    let out' := convWithPaddingStride' lhs' rhs' low high stride xdil ydil houtDim

    out' si


structure ConvolutionWithPaddingArgs {r} (lhsDims rhsDims outDims : Dims r) where

  window_strides : ArrayN ℕ+ (r-2)
  lowPadding : ArrayN ℤ (r-2)
  highPadding : ArrayN ℤ (r-2)
  lhs_dilation : ArrayN ℕ+ (r-2)
  rhs_dilation : ArrayN ℕ+ (r-2)
  window_reversal : ArrayN Bool (r-2)

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

  c1 : lhsDims.rank = r ∧ rhsDims.rank = r
  c2 : window_strides.size = r - 2
  c3 : ∀ d, (0:ℕ) < window_strides[d]
  c4 : lowPadding.size = r - 2 ∧ highPadding.size = r - 2
  c5 : lhs_dilation.size = r - 2
  c6 : ∀ d, (0:ℕ) < lhs_dilation[d]
  c7 : rhs_dilation.size = r - 2
  c8 : ∀ d, (0:ℕ) < rhs_dilation[d]
  c9 : window_reversal.size = r - 2
  c10 : lhsDims[input_batch_dimension] % batch_group_count = 0
  c11 : lhsDims[input_feature_dimension] % feature_group_count =  0
  c12 : input_spatial_dimensions.size = r - 2
  c13 : let input_dimensions := [input_batch_dimension] ++ input_spatial_dimensions.1.toList ++ [input_feature_dimension]
        input_dimensions.Nodup
        ∧
        (∀ (d : Fin (input_dimensions.length)), 0 ≤ input_dimensions[d].1 ∧ input_dimensions[d].1 < r)
  c14 : rhsDims[kernel_input_feature_dimension] = lhsDims[input_feature_dimension] / feature_group_count
  c15 : rhsDims[kernel_output_feature_dimension] % batch_group_count = 0
  c16 : rhsDims[kernel_output_feature_dimension] % feature_group_count = 0
  c17 : kernel_spatial_dimensions.size = r - 2
  c18 : let kernel_dimensions := [kernel_output_feature_dimension] ++ kernel_spatial_dimensions.1.toList ++ [kernel_input_feature_dimension]
        kernel_dimensions.Nodup
        ∧
        (∀ (d : Fin (kernel_dimensions.length)), 0 ≤ kernel_dimensions[d].1 ∧ kernel_dimensions[d].1 < r)
  c19 : output_spatial_dimensions.size = r - 2
  c20 : let output_dimensions := [output_batch_dimension] ++ output_spatial_dimensions.1.toList ++ [output_feature_dimension]
        output_dimensions.Nodup
        ∧
        (∀ (d : Fin (output_dimensions.length)), 0 ≤ output_dimensions[d].1 ∧ output_dimensions[d].1 < r)
  c21 : 0 < feature_group_count.1
  c22 : 0 < batch_group_count.1
  c23 : feature_group_count = 1 ∨ batch_group_count = 1
  c24 : True
  c25 : ∀ (result_dim : Fin r),
        outDims[result_dim]
        =
        if result_dim = output_batch_dimension then
          lhsDims[input_batch_dimension] / batch_group_count
        else if result_dim = output_feature_dimension then
          rhsDims[kernel_output_feature_dimension]
        else
          0
  c26 : outDims.rank = r
  c27 : True
  c28 : True
  c29 : True
  c30 : True
  c31 : True
  c32 : True
  c33 : True
  c34 : True


theorem ConvlutionWithPaddingArgs.feature_case {r} {lhsDims rhsDims outDims : Dims r}
    (args : ConvolutionWithPaddingArgs lhsDims rhsDims outDims) :
    args.feature_group_count > 1 →
    args.batch_group_count = 1
    ∧
    outDims[args.output_batch_dimension] = lhsDims[args.input_batch_dimension]
    ∧
    outDims[args.output_feature_dimension] = rhsDims[args.kernel_output_feature_dimension]
    := by
  intro h
  cases' args.c23 with h'
  · simp_all only [gt_iff_lt, lt_self_iff_false]
  · constructor
    · assumption
    · constructor
      · have := args.c25 args.output_batch_dimension
        simp_all
      · have := args.c25 args.output_feature_dimension
        have :  args.output_feature_dimension ≠ args.output_batch_dimension := sorry
        simp_all

theorem ConvlutionWithPaddingArgs.batch_case {r} {lhsDims rhsDims outDims : Dims r}
    (args : ConvolutionWithPaddingArgs lhsDims rhsDims outDims) :
    args.batch_group_count > 1 →
    args.feature_group_count = 1
    ∧
    rhsDims[args.kernel_input_feature_dimension] = lhsDims[args.input_feature_dimension]
    ∧
    outDims[args.output_batch_dimension] = lhsDims[args.input_batch_dimension] / args.batch_group_count
    ∧
    outDims[args.output_feature_dimension] = rhsDims[args.kernel_output_feature_dimension]
    := by
  intro h
  cases' args.c23 with h'
  · constructor
    · assumption
    · constructor
      · have := args.c14
        simp_all
      · constructor
        · have := args.c25 args.output_batch_dimension
          simp_all
        · have := args.c25 args.output_feature_dimension
          have :  args.output_feature_dimension ≠ args.output_batch_dimension := sorry
          simp_all
  · aesop



def ConvolutionWithPaddingArgs.lhsAdjoint {r} {lhsDims rhsDims outDims : Dims r}
    (args : ConvolutionWithPaddingArgs lhsDims rhsDims outDims) :
    ConvolutionWithPaddingArgs outDims rhsDims lhsDims :=

  let kerDims  : ArrayN ℤ (r-2) := sorry
  let kerDims' := kerDims*args.rhs_dilation
  {
    window_strides := args.lhs_dilation
    lowPadding := kerDims' - args.lowPadding - 1
    highPadding := kerDims' - args.highPadding - 1
    lhs_dilation := args.window_strides
    rhs_dilation := args.rhs_dilation
    window_reversal := args.window_reversal

    input_batch_dimension := args.output_batch_dimension
    input_feature_dimension := args.output_feature_dimension
    input_spatial_dimensions := args.output_spatial_dimensions

    kernel_input_feature_dimension := args.kernel_input_feature_dimension
    kernel_output_feature_dimension := args.kernel_output_feature_dimension
    kernel_spatial_dimensions := args.kernel_spatial_dimensions

    output_batch_dimension := args.input_batch_dimension
    output_feature_dimension := args.input_feature_dimension
    output_spatial_dimensions := args.input_spatial_dimensions

    feature_group_count := 1 -- args.feature_group_count
    batch_group_count := args.batch_group_count

    c1 := by simp
    c2 := by simp
    c3 := by simp
    c4 := by simp
    c5 := by simp
    c6 := by simp
    c7 := by simp
    c8 := by simp
    c9 := by simp
    c10 := by have := args.c25 args.output_batch_dimension; simp_all; sorry
    c11 := by have := args.c25 args.output_feature_dimension; simp_all; sorry
    c12 := by simp
    c13 := by exact args.c20
    c14 := by
      -- we know:
      --   outDims[args.output_feature_dimension] = rhsDims[kernel_output_feature_dimension]
      --   rhsDims[kernel_input_feature_dimension] = lhsDims[input_feature_dimension] / feature_group_count
      -- rhsDims[args.kernel_input_feature_dimension] = outDims[args.output_feature_dimension] / ↑↑args.feature_group_count

      simp [args.c25 args.output_feature_dimension,
            (sorry : args.output_feature_dimension ≠ args.output_batch_dimension)]
      sorry
    c15 := by exact args.c15
    c16 := by exact args.c16
    c17 := by simp
    c18 := by exact args.c18
    c19 := by simp
    c20 := by exact args.c13
    c21 := by cases args; simp_all
    c22 := by cases args; simp_all
    c23 := by cases args; simp_all
    c24 := by simp
    c25 := by
      intro result_dim
      by_cases h : (result_dim = args.input_batch_dimension)
      · simp[h]
        -- lhsDims[args.input_batch_dimension] = outDims[args.output_batch_dimension] / ↑↑args.batch_group_count
        sorry
      · simp[h]
        by_cases h' : (result_dim = args.input_feature_dimension)
        · have := args.c25 result_dim
          simp_all [h,h']
          -- lhsDims[args.input_feature_dimension] = rhsDims[args.kernel_output_feature_dimension]
          sorry
        · simp_all [h,h']
          sorry
    c26 := by simp
    c27 := by simp
    c28 := by simp
    c29 := by simp
    c30 := by simp
    c31 := by simp
    c32 := by simp
    c33 := by simp
    c34 := by simp
  }


def ConvolutionWithPaddingArgs.rhsAdjoint {r} {lhsDims rhsDims outDims : Dims r}
    (args : ConvolutionWithPaddingArgs lhsDims rhsDims outDims) :
    ConvolutionWithPaddingArgs outDims rhsDims lhsDims where



-- open Set in
-- def convolutionB {lhsDims rhsDims : Dims (r+2)}
--    (lhs : TensorIndex lhsDims → R) (rhs : TensorIndex rhsDims → R)
--    (outDims : Dims (r+2)) (args : ConvolutionWithPaddingArgs lhsDims rhsDims outDims) : TensorIndex outDims → R := sorry

-- If feature_group_count = 1 and batch_group_count = 1, then for all output_spatial_index in index_space(dim(result, output_spatial_dimensions...)), result[result_shape(:, output_spatial_index, :)] = dot_product where:

-- padding_value = constant(0, element_type(lhs)).
-- padded_lhs = pad(lhs, padding_value, lhs_padding[:, 0], lhs_padding[:, 1], lhs_base_dilations - 1).
-- lhs_window_start = lhs_shape(0, output_spatial_index, 0) * lhs_window_strides.
-- lhs_window = slice(padded_lhs, lhs_window_start, lhs_window_start + lhs_window_dimensions, lhs_window_dilations).
-- reversed_lhs_window = reverse(lhs_window, [input_spatial_dimensions[dim] for dim in range(size(window_reversal)) if window_reversal[dim] = true]). This feature appears to be unused, so in the future we are planning to remove it (#1181).
-- dot_product = dot_general(reversed_lhs_window, rhs, lhs_batching_dimensions=[], lhs_contracting_dimensions=input_spatial_dimensions + [input_feature_dimension], rhs_batching_dimensions=[], rhs_contracting_dimensions=kernel_spatial_dimensions + [kernel_input_feature_dimension]).


def slice.outDims {r}
    (start_indices limit_indices : ArrayN ℤ r)
    (strides : ArrayN ℕ+ r) : ArrayN ℤ r := (limit_indices - start_indices + (strides.toInt - 1)) / strides.toInt

-- ceil((limit_indices - start_indices) / strides)

def slice {r} {inDims outDims : Dims r}
    (operand : TensorIndex inDims → R)
    (start_indices limit_indices : ArrayN ℤ r)
    (strides : ArrayN ℕ+ r)
    (houtDims : outDims = slice.outDims start_indices limit_indices strides := by infer_var) :
    TensorIndex outDims → R :=
  fun result_index =>
    let operand_index := start_indices.toInt + result_index.1 * strides
    operand ⟨operand_index, sorry⟩

-- result[result_index] = operand[operand_index] where

@[simp]
theorem ArrayN.data_size {n α} (a : ArrayN α n) : a.data.size = n := by simp[a.2]

def convolutionBase {r} {lhsDims rhsDims outDims : Dims r}
    (lhs : TensorIndex lhsDims → R)
    (rhs : TensorIndex rhsDims → R)
    (args : ConvolutionWithPaddingArgs lhsDims rhsDims outDims) :
    TensorIndex outDims → R :=

  fun i =>
    let output_spatial_index : ArrayN ℤ (r-2) := sorry -- get the correct parts of `i`
    let lhs_shape : ∀ {α}, α → ArrayN α (r - 2) → α → ArrayN α r := sorry

    let lhs_window_dimensions :=
      lhs_shape (lhsDims[args.input_batch_dimension])
                (.ofFn (fun i => rhsDims[args.kernel_spatial_dimensions[i]]))
                (lhsDims[args.input_feature_dimension])
    let lhs_window_strides := lhs_shape 1 args.window_strides 1
    let lhs_padding_low  := lhs_shape 0 args.lowPadding 0
    let lhs_padding_high := lhs_shape 0 args.highPadding 0
    let lhs_base_dilation := lhs_shape 1 args.lhs_dilation 1
    let lhs_window_dilations := lhs_shape 1 args.rhs_dilation 1


    let padded_lhs := pad lhs 0 lhs_padding_low lhs_padding_high lhs_base_dilation.toNat (outDims:= pad.outDims lhsDims lhs_padding_low lhs_padding_high lhs_base_dilation.toNat) (by infer_var)
    let lhs_window_start : ArrayN ℤ r := lhs_shape 0 output_spatial_index 0
    let lhs_window := slice padded_lhs lhs_window_start (lhs_window_start + lhs_window_dimensions) lhs_window_dilations
                        (outDims:=slice.outDims lhs_window_start (lhs_window_start + lhs_window_dimensions) lhs_window_dilations) (by infer_var)
    let dot_product : R :=
      dot_general lhs_window rhs
        {lhs_batching_dimensions := #[]
         rhs_batching_dimensions := #[]
         lhs_contracting_dimensions := args.input_spatial_dimensions.1 ++ [args.input_feature_dimension]
         rhs_contracting_dimensions := args.kernel_spatial_dimensions.1 ++ [args.kernel_input_feature_dimension]

         c1 := by simp
         c2 := by simp
         c3 := by have := args.c13.1; simp_all
         c4 := by have := args.c18.1; simp_all
         c5 := by simp
         c6 := by simp
         c7 := by simp
         c8 := by simp
         c9 := by intro d; simp at d; have := d.2; aesop
         c10 := by sorry
         c11 := by simp
         c12 := by sorry}
        (t:= 0) (outDims := sorry) sorry

    dot_product
