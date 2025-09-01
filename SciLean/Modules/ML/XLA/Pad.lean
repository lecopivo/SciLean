import SciLean.Modules.ML.XLA.TensorIndex
import SciLean.Meta.GenerateFunTrans
import SciLean.Meta.GenerateFunProp

import Mathlib.Tactic.ProxyType

namespace SciLean

/-! StableHLO function: `pad`

Spec: (source: https://github.com/openxla/stablehlo/blob/main/docs/spec.md)

### pad

#### Semantics

Expands `operand` by padding around the tensor as well as between the elements
of the tensor with the given `padding_value`.

`edge_padding_low` and `edge_padding_high` specify the amount of padding added
at the low-end (next to index 0) and the high-end (next to the highest index) of
each dimension respectively. The amount of padding can be negative, where the
absolute value of negative padding indicates the number of elements to remove
from the specified dimension.

`interior_padding` specifies the amount of padding added between any two
elements in each dimension which may not be negative. Interior padding occurs
before edge padding such that negative edge padding will remove elements from
the interior-padded operand.

More formally, `result[result_index]` is defined as:

* `operand[operand_index]` if
  `result_index = edge_padding_low + operand_index * (interior_padding + 1)`.
* `padding_value` otherwise.

#### Inputs

| Label | Name                | Type                                                | Constraints      |
|-------|---------------------|-----------------------------------------------------|------------------|
| (I1)  | `operand`           | tensor or per-tensor quantized tensor               | (C1), (C2), (C4) |
| (I2)  | `padding_value`     | 0-dimensional tensor or per-tensor quantized tensor | (C1)             |
| (I3)  | `edge_padding_low`  | 1-dimensional tensor constant of type `si64`        | (C1), (C4)       |
| (I4)  | `edge_padding_high` | 1-dimensional tensor constant of type `si64`        | (C1), (C4)       |
| (I5)  | `interior_padding`  | 1-dimensional tensor constant of type `si64`        | (C2-C4)          |

#### Outputs

| Name     | Type                                  | Constraints |
|----------|---------------------------------------|-------------|
| `result` | tensor or per-tensor quantized tensor | (C3-C6)     |

#### Constraints

* (C1) `element_type(operand) = element_type(padding_value) =
  element_type(result)`.
* (C2) `size(edge_padding_low) = size(edge_padding_high) =
  size(interior_padding) = rank(operand)`.
* (C3) `0 <= interior_padding`.
* (C4) `shape(result) = shape(operand) + edge_padding_low +
  max(shape(operand) - 1, 0) * interior_padding + edge_padding_high`.

#### Examples

```mlir
// %operand: [
//            [1, 2, 3],
//            [4, 5, 6]
//           ]
// %padding_value: 0
%result = "stablehlo.pad"(%operand, %padding_value) {
  edge_padding_low = array<i64: 0, 1>,
  edge_padding_high = array<i64: 2, 1>,
  interior_padding = array<i64: 1, 2>
} : (tensor<2x3xi32>, tensor<i32>) -> tensor<5x9xi32>
// %result: [
//           [0, 1, 0, 0, 2, 0, 0, 3, 0],
//           [0, 0, 0, 0, 0, 0, 0, 0, 0],
//           [0, 4, 0, 0, 5, 0, 0, 6, 0],
//           [0, 0, 0, 0, 0, 0, 0, 0, 0],
//           [0, 0, 0, 0, 0, 0, 0, 0, 0]
//          ]
```

&nbsp;[More Examples](https://github.com/openxla/stablehlo/tree/main/stablehlo/tests/interpret/pad.mlir)


-/



namespace Pad

structure Args {r} (inDims : Dims r) where
  edge_padding_low  : ArrayN ℤ r
  edge_padding_high : ArrayN ℤ r
  interior_padding : ArrayN ℕ r

def Args.outShape {r} {inDims : Dims r} (args : Args inDims) : Dims r :=
  inDims
  + args.edge_padding_low
  + ((inDims - 1) ⊔ 0) * args.interior_padding.toInt
  + args.edge_padding_high


@[ext]
structure Conditions {r} {inDims : Dims r} (args : Args inDims) (outDims : Dims r) : Prop where
  c1 : True
  c2 : args.edge_padding_low.size = r
       ∧ args.edge_padding_high.size = r
       ∧ args.interior_padding.size = r
  c3 : 0 ≤ args.interior_padding
  c4 : outDims = inDims
         + args.edge_padding_low
         + ((inDims - 1) ⊔ 0) * args.interior_padding.toInt
         + args.edge_padding_high


instance : Decidable (Conditions args outDims) :=
  if h : outDims = args.outShape then
    .isTrue (by constructor
                · exact True.intro
                · simp
                · intro d; simp
                · exact h)
  else
    .isFalse (by intro h'; exact h (h'.c4))


end Pad

def pad
    {R} [RealScalar R]
    {r} {inDims outDims : Dims r}
    (operand : TensorIndex inDims → R)
    (padding_value : R)
    (args : Pad.Args inDims)
    (houtDims : outDims = args.outShape := by infer_var) :
    TensorIndex outDims → R :=

  fun i =>
    let di := (i.1 - args.edge_padding_low) / args.interior_padding.toInt
    let ri := (i.1 - args.edge_padding_low) % args.interior_padding.toInt
    if h : (0 ≤ di ∧ di < inDims) ∧ (ri = 0) then
      operand ⟨di, by intro d; have := h.1.1 d; have := h.1.2 d; simp_all⟩
    else
      padding_value


def_fun_prop pad in operand padding_value
  with_transitive
  : IsContinuousLinearMap R by unfold pad; fun_prop


-- Can we express this function by a XLA function?
def pad.arg_operand.adjoint
    {R} [RealScalar R]
    {r} {inDims outDims : Dims r}
    (output : TensorIndex outDims → R)
    (args : Pad.Args inDims)
    (houtDims : outDims = args.outShape) :
    TensorIndex inDims → R :=
  fun di =>
    let i := di.1 * args.interior_padding.toInt + args.edge_padding_low
    if h : (0 ≤ i ∧ i < outDims) then
      output ⟨i, by intro d; have := h.1 d; have := h.2 d; simp_all⟩
    else
      0


-- Can we express this function by a XLA function?
-- Probably dot_general?
def pad.arg_padding_value.adjoint
    {R} [RealScalar R]
    {r} {inDims outDims : Dims r}
    (output : TensorIndex outDims → R)
    (args : Pad.Args inDims)
    (houtDims : outDims = args.outShape) :
    R :=
  ∑ i : TensorIndex outDims,
    let di := (i.1 - args.edge_padding_low) / args.interior_padding.toInt
    let ri := (i.1 - args.edge_padding_low) % args.interior_padding.toInt
    if ¬((0 ≤ di ∧ di < inDims) ∧ (ri = 0)) then
      output i
    else
      0


@[fun_trans]
theorem pad.arg_operandpadding_value.adjoint_rule
    {R} [RealScalar R]
    {r} {inDims outDims : Dims r}
    (args : Pad.Args inDims)
    (houtDims : outDims = args.outShape) :
    adjoint R (fun xy : (TensorIndex inDims → R)×R => pad xy.1 xy.2 args houtDims)
    =
    fun z =>
      (pad.arg_operand.adjoint z args houtDims,
       pad.arg_padding_value.adjoint z args houtDims) := by

  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro z y
  simp (config:={zeta:=false}) only [simp_core,Inner.inner,pad,arg_operand.adjoint,arg_padding_value.adjoint]
  symm
  calc
    _ = ∑ (i : TensorIndex outDims), z i *
        let di := (i.val - args.edge_padding_low) / args.interior_padding.toInt;
        let ri := (i.val - args.edge_padding_low) % args.interior_padding.toInt;
        if h : (0 ≤ di ∧ di < inDims) ∧ ri = 0 then y.1 ⟨di, sorry⟩
        else y.2 := by rfl

    _ = (∑ (i : TensorIndex outDims), z i *
        let di := (i.val - args.edge_padding_low) / args.interior_padding.toInt;
        let ri := (i.val - args.edge_padding_low) % args.interior_padding.toInt;
        if h : (0 ≤ di ∧ di < inDims) ∧ ri = 0 then y.1 ⟨di, sorry⟩
        else 0)
        +
        (∑ (i : TensorIndex outDims), z i *
        let di := (i.val - args.edge_padding_low) / args.interior_padding.toInt;
        let ri := (i.val - args.edge_padding_low) % args.interior_padding.toInt;
        if ¬((0 ≤ di ∧ di < inDims) ∧ ri = 0) then y.2
        else 0) := by sorry


    _ = (∑ (di : TensorIndex inDims),
        let i := di.1 * args.interior_padding.toInt + args.edge_padding_low
        (if 0 ≤ i ∧ i < outDims then
          z ⟨i,sorry⟩
        else
          0) * y.1 di)
        +
        (∑ (i : TensorIndex outDims),
        let di := (i.val - args.edge_padding_low) / args.interior_padding.toInt;
        let ri := (i.val - args.edge_padding_low) % args.interior_padding.toInt;
        if ¬((0 ≤ di ∧ di < inDims) ∧ ri = 0) then z i
        else 0) * y.2 := by sorry

    _ = _ := by rfl
