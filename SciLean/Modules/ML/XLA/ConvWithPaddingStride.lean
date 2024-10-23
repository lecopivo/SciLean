import SciLean.Modules.ML.XLA.ConvWithPadding
import SciLean.Meta.GenerateFunTrans
import SciLean.Tactic.LetUtils
import SciLean.Tactic.CompiledTactics

namespace SciLean


variable {R} [RealScalar R] [PlainDataType R]



/-- output dimension of convolution give strides and dilations -/
def convOutDim {r} (sp ker : ArrayN ℤ r) (low high : ArrayN ℤ r) (stride xdil ydil : ArrayN ℕ+ r) : ArrayN ℤ r :=
  let sp' := (sp - 1) * xdil + 1 + low + high
  let ker' := (ker - 1) * ydil + 1
  (sp' - ker') / stride + 1


theorem t1 (z : ℤ) (y : ℕ+) : z / (y:ℤ) * y = z - z % y := by sorry
theorem t2 (z x : ℤ) (y w : ℕ+) (h : w ≤ y) : (z * y + (- y - x % w)) / (y:ℤ) = z - 1 := by sorry
theorem t3 (z x : ℤ) (y w : ℕ+) (h : w ≤ y) : (z * y - y + x % w) / (y:ℤ) = z - 1 := by sorry

/-- theorem to check correctness of output dimension of adjoint convolution. -/
theorem outDim_swap {r} {sp ker : ArrayN ℤ r} {low high : ArrayN ℤ r} {stride xdil ydil : ArrayN ℕ+ r} (h : stride ≤ xdil) :
    let ker' := (ker-1)*ydil+1
    convOutDim (convOutDim sp ker low high stride xdil ydil) ker (ker'-low-1) (ker'-high-1) xdil stride ydil
    =
    sp := by
  unfold convOutDim
  ext d
  simp
  rw[t1]
  ring_nf
  rw[t2 _ _ _ _ (h d)]
  ring

/-- theorem to check correctness of output dimension of adjoint convolution. -/
theorem outDim_swap' {r} {spDims kerDims : ArrayN ℤ r} {low high : ArrayN ℤ r} {stride xdil ydil : ArrayN ℕ+ r} (h : stride ≤ ydil) :
    convOutDim spDims (convOutDim spDims kerDims low high stride xdil ydil) low high ydil xdil stride
    =
    kerDims := by
  unfold convOutDim
  ext d
  simp
  rw[t1]
  ring_nf
  rw[t3 _ _ _ _ (h d)]
  ring


def convWithPaddingStride
    {spDims kerDims : Dims r}
    (x : R^[TensorIndex spDims]) (y : R^[TensorIndex kerDims])  -- lhs and rhs
    (low high : ArrayN ℤ r)    -- padding
    (stride : ArrayN ℕ+ r)    -- window stride
    (xdil ydil : ArrayN ℕ+ r) -- dillatation
    {outDim : Dims r}
    (houtDim : outDim = convOutDim spDims kerDims low high stride xdil ydil := by unfold convOutDim; reduce_dim) :
    R^[TensorIndex outDim] :=
  ⊞ (i : TensorIndex outDim) =>
    ∑ (j : TensorIndex kerDims),
      let k := i.1 * stride + j.1 * ydil - low
      let dk := k / xdil
      let rk := k % xdil
      if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
        have := h.1
        x[dk] * y[j]
      else
        0


def convWithPaddingStride'
    {spDims kerDims : Dims r}
    (x : TensorIndex spDims → R) (y : TensorIndex kerDims → R)  -- lhs and rhs
    (low high : ArrayN ℤ r)    -- padding
    (stride : ArrayN ℕ+ r)    -- window stride
    (xdil ydil : ArrayN ℕ+ r) -- dillatation
    {outDim : Dims r}
    (houtDim : outDim = convOutDim spDims kerDims low high stride xdil ydil := by unfold convOutDim; reduce_dim) :
    TensorIndex outDim → R :=
  fun (i : TensorIndex outDim) =>
    ∑ (j : TensorIndex kerDims),
      let k := i.1 * stride + j.1 * ydil - low
      let dk := k / xdil
      let rk := k % xdil
      if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
        have := h.1
        x ⟨dk, by intro d; have := h.1.1 d; have := h.1.2 d; simp_all⟩ * y j
      else
        0


def_fun_prop convWithPaddingStride in x
  : IsContinuousLinearMap R by unfold convWithPaddingStride; dsimp; fun_prop

def_fun_prop convWithPaddingStride in y
  : IsContinuousLinearMap R by unfold convWithPaddingStride; dsimp; fun_prop

def_fun_prop convWithPaddingStride' in x
  : IsContinuousLinearMap R by unfold convWithPaddingStride'; dsimp; fun_prop

def_fun_prop convWithPaddingStride' in y
  : IsContinuousLinearMap R by unfold convWithPaddingStride'; dsimp; fun_prop


@[fun_trans]
theorem convWithPaddingStride.arg_y.adjoint_rule
    {spDims kerDims : Dims r}
    (x : R^[TensorIndex spDims])
    (low high : ArrayN ℤ r)    -- padding
    (stride : ArrayN ℕ+ r)    -- window stride
    (xdil ydil : ArrayN ℕ+ r) -- dillatation
    (hstride : stride ≤ ydil)
    {outDim : Dims r}
    (houtDim : outDim = convOutDim spDims kerDims low high stride xdil ydil) :
    adjoint R (fun y => convWithPaddingStride x y low high stride xdil ydil houtDim)
    =
    fun z => convWithPaddingStride x z low high ydil xdil stride
               (by rw[houtDim,outDim_swap' hstride]) := by

  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro z y
  simp (config:={zeta:=false}) [Inner.inner,convWithPaddingStride]
  symm
  calc
    _ = ∑ (i : TensorIndex outDim), z[i] * ∑ (j : TensorIndex kerDims),
      let k := i.1 * stride + j.1 * ydil - low
      let dk := k / xdil
      let rk := k % xdil
      if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
        have := h.1
        x[dk] * y[j]
      else
        0 := by rfl

    _ = ∑ (i : TensorIndex outDim), ∑ (j : TensorIndex kerDims),
      let k := i.1 * stride + j.1 * ydil - low
      let dk := k / xdil
      let rk := k % xdil
      if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
        have := h.1
        x[dk] * z[i] * y[j]
      else
        0 := by sorry -- move `z` in

    _ = ∑ (j : TensorIndex kerDims), ∑ (i : TensorIndex outDim),
      let k := i.1 * stride + j.1 * ydil - low
      let dk := k / xdil
      let rk := k % xdil
      if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
        have := h.1
        x[dk] * z[i] * y[j]
      else
        0 := by sorry -- swap sums

    _ = ∑ (j : TensorIndex kerDims), (∑ (i : TensorIndex outDim),
      let k := j.1 * ydil + i.1 * stride - low
      let dk := k / xdil
      let rk := k % xdil
      if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
        have := h.1
        x[dk] * z[i]
      else
        0) * y[j] := by sorry -- move `y[j]` out and swap `i.1 * stride + j.1 * ydil`

    _ = _ := by rfl


@[fun_trans]
theorem convWithPaddingStride.arg_x.adjoint_rule
    {spDims kerDims : Dims r}
    (y : R^[TensorIndex kerDims])
    (low high : ArrayN ℤ r)    -- padding
    (stride : ArrayN ℕ+ r)    -- window stride
    (xdil ydil : ArrayN ℕ+ r) -- dillatation
    {outDim : Dims r}
    (hstride : stride ≤ xdil)
    (houtDim : outDim = convOutDim spDims kerDims low high stride xdil ydil) :
    adjoint R (fun x => convWithPaddingStride x y low high stride xdil ydil houtDim)
    =
    let ker' := (kerDims-1)*ydil+1
    fun z => convWithPaddingStride z (rev y) (ker'-low-1) (ker'-high-1) xdil stride ydil
               (by rw[houtDim,outDim_swap hstride]) := by

  rw[← (eq_adjoint_iff _ _ (by fun_prop)).2]
  intro z x
  sorry

   -- some linker issue with lsimp, commenting it out for now

  -- lsimp (config:={zeta:=false}) [Inner.inner,convWithPaddingStride]
  -- intro ker'
  -- symm
  -- calc
  --   _ = ∑ (i : TensorIndex outDim), z[i] * ∑ (j : TensorIndex kerDims),
  --     let k := i.1 * stride + j.1 * ydil - low
  --     let dk := k / xdil
  --     let rk := k % xdil
  --     if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
  --       have := h.1
  --       x[dk] * y[j]
  --     else
  --       0 := by rfl

  --   _ = ∑ (i : TensorIndex outDim), ∑ (j : TensorIndex kerDims),
  --     let k := i.1 * stride + j.1 * ydil - low
  --     let dk := k / xdil
  --     let rk := k % xdil
  --     if h : (0 ≤ dk ∧ dk < spDims) ∧ (rk = 0) then
  --       have := h.1
  --       z[i] * x[dk] * y[j]
  --     else
  --       0 := by sorry -- move `z` in

  --   _ = ∑ (i : TensorIndex outDim), ∑ (j : TensorIndex kerDims), ∑ (k : TensorIndex spDims),
  --     if k.1 * xdil = i.1 * stride + j.1 * ydil - low then
  --       z[i] * x[k] * y[j]
  --     else 0 := by sorry -- introduce sum over `k`

  --   _ = ∑ (k : TensorIndex spDims), ∑ (j : TensorIndex kerDims), ∑ (i : TensorIndex outDim),
  --     let i' := k.1 * xdil - j.1 * ydil + low
  --     let di' := i' / stride
  --     let ri' := i' % stride
  --     if i.1 = di' ∧ ri' = 0 then
  --       z[i] * x[k] * y[j]
  --     else 0 := by sorry -- swap sums and rewrite the condition in terms of `i'`


  --   _ = ∑ (k : TensorIndex spDims), ∑ (j : TensorIndex kerDims),
  --     let i' := k.1 * xdil - j.1 * ydil + low
  --     let di' := i' / stride
  --     let ri' := i' % stride
  --     if h : (0 ≤ di' ∧ di' < outDim) ∧ (ri' = 0) then
  --       have := h.1
  --       z[di'] * x[k] * y[j]
  --     else 0 := by sorry -- remove sum over `i`

  --   _ = ∑ (k : TensorIndex spDims), ∑ (j : TensorIndex kerDims),
  --     let i' := k.1 * xdil + j.1 * ydil - ((kerDims - 1) * ydil - low)
  --     let di' := i' / stride
  --     let ri' := i' % stride
  --     if h : (0 ≤ di' ∧ di' < outDim) ∧ (ri' = 0) then
  --       have := h.1
  --       z[di'] * x[k] * (rev y)[j]
  --     else 0 := by sorry -- reverse the sum over `j`, `j --> kerDims - 1 - j`

  --   _ = ∑ (k : TensorIndex spDims), (∑ (j : TensorIndex kerDims),
  --     let i' := k.1 * xdil + j.1 * ydil - ((kerDims - 1) * ydil + 1 - low - 1)
  --     let di' := i' / stride
  --     let ri' := i' % stride
  --     if h : (0 ≤ di' ∧ di' < outDim) ∧ (ri' = 0) then
  --       have := h.1
  --       z[di'] * (rev y)[j]
  --     else 0) * x[k] := by sorry -- move x[k] out

  --   _ = _ := by  rfl


-- def_fun_trans convWithPaddingStride in x
--   (hstride : stride ≤ xdil) : revFDeriv R by
--     rw[revFDeriv_linear _ (by fun_prop)]
--     autodiff (disch:=assumption)


-- def_fun_trans convWithPaddingStride in y
--   (hstride : stride ≤ ydil) : revFDeriv R by
--     rw[revFDeriv_linear _ (by fun_prop)]
--     autodiff (disch:=assumption)
