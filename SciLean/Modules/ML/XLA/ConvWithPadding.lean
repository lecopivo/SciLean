import SciLean.Modules.ML.XLA.TensorIndex
import SciLean.Data.DataArray
import SciLean.Data.FinProd
import SciLean.Tactic.InferVar
import SciLean.Analysis.Normed.IsContinuousLinearMap
import SciLean.Analysis.Scalar.FloatAsReal
import SciLean.Data.ArrayType

namespace SciLean


variable {R} [RealScalar R] [PlainDataType R]


theorem ArrayType.lt_elemwise {Cont Idx Elem} [ArrayType Cont Idx Elem] [LT Elem] {x y : Cont} :
   (∀ i, x[i] < y[i]) → x < y := id

theorem ArrayType.le_elemwise {Cont Idx Elem} [ArrayType Cont Idx Elem] [LE Elem] {x y : Cont} :
   (∀ i, x[i] ≤ y[i]) → x ≤ y := id


macro "tensor_index_bounds" i:term : tactic =>
  `(tactic|
     (constructor
      · apply ArrayType.le_elemwise; intro d; simp; have := ($i).2 d; omega;
      · apply ArrayType.lt_elemwise; intro d; simp; have := ($i).2 d; omega))

instance {r} {dim : Dims r} : GetElem (DataArrayN R (TensorIndex dim)) (Vector ℤ r) R (fun _ i => 0 ≤ i ∧ i < dim) where
  getElem x i h := x[⟨i, by intro d; have h1 := h.1 d; have h2 := h.2 d; simp_all⟩]

@[fun_prop]
theorem getElem_clm {r} {dim : Dims r} (i : Vector ℤ r) (h : 0 ≤ i ∧ i < dim) :
    IsContinuousLinearMap R (fun x : DataArrayN R (TensorIndex dim) => x[i]'h) := sorry

macro "reduce_dim" : tactic => `(tactic|
  first | simp_all | ((try simp); infer_var) | (ext i; simp; ring))


def convWithPadding {spDims kerDims : Dims r}
    (x : R^[TensorIndex spDims]) (y : R^[TensorIndex kerDims]) (low high : Vector ℤ r)
    {outDim : Dims r} (houtDim : outDim = (spDims - kerDims + low + high + 1):= by reduce_dim) :
    R^[TensorIndex outDim] :=
  ⊞ (i : TensorIndex outDim) =>
    ∑ (j : TensorIndex kerDims),
      let i' := i.1 + j.1 - low
      if h : 0 ≤ i' ∧ i' < spDims then
        x[i'] * y[j]
      else
        0



@[fun_trans]
theorem convWithPadding.arg_y.adjoint_rule {r} {spDims kerDims : Dims r}
    (x : R^[TensorIndex spDims]) (l h : Vector ℤ r)
    {outDim : Dims r} (houtDim : outDim = (spDims - kerDims + l + h + 1)) :
    (adjoint R (fun (y : R^[TensorIndex kerDims]) => convWithPadding x y l h houtDim))
    =
    fun z => convWithPadding x z l h (by rw[houtDim]; ext i; simp; ring) := by

  rw[← (eq_adjoint_iff _ _ (by unfold convWithPadding; fun_prop)).2]
  intro z y
  simp (config:={zeta:=false}) [Inner.inner,convWithPadding]
  symm
  calc
    _ = ∑ (i : TensorIndex outDim), z[i] * ∑ j,
          let i' := i.1 + j.1 - l
          if h : 0 ≤ i' ∧ i' < spDims then
            x[i'] * y[j]
          else
            0 := by rfl

    _ = ∑ (i : TensorIndex outDim), ∑ j,
          let i' := i.1 + j.1 - l
          if h : 0 ≤ i' ∧ i' < spDims then
            x[i'] * z[i] *  y[j]
          else
            0 := by sorry -- move `z` in

    _ = ∑ j, ∑ (i : TensorIndex outDim),
          let i' := i.1 + j.1 - l
          if h : 0 ≤ i' ∧ i' < spDims then
            x[i'] * z[i] *  y[j]
          else
            0 := by sorry -- swap sums

    _ = ∑ j, (∑ (i : TensorIndex outDim),
          let i' := j.1 + i.1 - l
          if h : 0 ≤ i' ∧ i' < spDims then
            x[i'] * z[i]
          else
            0) * y[j] := by sorry -- move `y[j]` out and swap `i.1 + j.1`

    _ = _ := rfl


def rev {r} {dim : Dims r} (x : R^[TensorIndex dim]) :
    R^[TensorIndex dim] :=
  ⊞ (i : TensorIndex dim) => x[dim - 1 - i.1]'(by tensor_index_bounds i)


@[fun_trans]
theorem convWithPadding.arg_x.adjoint_rule {r} {spDims kerDims : Dims r}
    (y : R^[TensorIndex kerDims]) (l h : Vector ℤ r)
    {outDim : Dims r} (houtDim : outDim = (spDims - kerDims + l + h + 1)) :
    (adjoint R (fun (x : R^[TensorIndex spDims]) => convWithPadding x y l h houtDim))
    =
    fun z : R^[TensorIndex outDim] => convWithPadding z (rev y) (kerDims-l-1) (kerDims-h-1) (by rw[houtDim]; ext i; simp; ring) := by

  rw[← (eq_adjoint_iff _ _ (by unfold convWithPadding; fun_prop)).2]
  intro z x
  simp[Inner.inner,convWithPadding]
  symm
  calc
    _ = ∑ (i : TensorIndex outDim), z[i] * ∑ (j : TensorIndex kerDims),
          let k := i.1 + j.1 - l
          if h : 0 ≤ k ∧ k < spDims then
            x[k] * y[j]
          else 0 := by rfl

    _ = ∑ (i : TensorIndex outDim), ∑ (j : TensorIndex kerDims),
          let k := i.1 + j.1 - l
          if h : 0 ≤ k ∧ k < spDims then
            z[i] * x[k] * y[j]
          else 0 := by sorry -- move `z` in

    _ = ∑ (i : TensorIndex outDim), ∑ (j : TensorIndex kerDims), ∑ (k : TensorIndex spDims),
          if k.1 = i.1 + j.1 - l then
            z[i] * x[k] * y[j]
          else 0 := by sorry -- introduce sum over `k`

    _ = ∑ (k : TensorIndex spDims), ∑ (j : TensorIndex kerDims), ∑ (i : TensorIndex outDim),
          if i.1 = k.1 - j.1 + l then
            z[i] * x[k] * y[j]
          else 0 := by sorry -- reshuffle sums and condition

    _ = ∑ (k : TensorIndex spDims), ∑ (j : TensorIndex kerDims),
          let i := k.1 - j.1 + l
          if h : 0 ≤ i ∧ i < outDim then
            z[i] * x[k] * y[j]
          else 0 := by sorry -- remove sum over i

    _ = ∑ (k : TensorIndex spDims), ∑ (j : TensorIndex kerDims),
          let i := k.1 - (kerDims - 1 - j.1) + l
          if h : 0 ≤ i ∧ i < outDim then
            z[i] * x[k] * (rev y)[j]
          else 0 := by sorry -- substitution `j --> kerDims - 1 - j

    _ = ∑ (k : TensorIndex spDims), (∑ (j : TensorIndex kerDims),
          let i := k.1 + j.1 - (kerDims - l - 1)
          if h : 0 ≤ i ∧ i < outDim then
            z[i] * (rev y)[j]
          else 0) * x[k] := by sorry -- move `x[k]` out and clean up `i'`

    _ = _ := by rfl



#check Mod
