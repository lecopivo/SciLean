import SciLean.Modules.ML.XLA.TensorIndex
import SciLean.Modules.ML.XLA.Concatenate


namespace SciLean

/-! Split function that is not in StableHLO spec but appears in the definition of convolution

-/


namespace Split

structure Args {r} (inDims : Dims r) where
  split_size : ℕ+
  split_dimension : Fin r

def Args.outShape {r} {inDims : Dims r} (args : Args inDims) : Dims r :=
  .ofFn fun d =>
    if d = args.split_dimension then
      inDims[d] / args.split_size
    else
      inDims[d]

def Args.indexMap {r} {inDims : Dims r} (args : Args inDims) :
  Fin args.split_size × TensorIndex args.outShape
  ≃
  TensorIndex inDims := sorry

structure Conditions {r} {inDims : Dims r} (args : Args inDims) (outDims : Dims r) where
  c1 : inDims[args.split_dimension] % args.split_size = 0
  c2 : ∀ d,
    if d = args.split_dimension then
      outDims[d] = inDims[d] / args.split_size
    else
      outDims[d] = inDims[d]

structure Args' {r} (inDims outDims : Dims r)

end Split

open Split in

def split {r} {inDims outDims : Dims r} (operand : TensorIndex inDims → R)
    (args : Args inDims) (h : Conditions args outDims)
    (houtDims : outDims = args.outShape := by infer_var)
    (i : Fin args.split_size) : TensorIndex outDims → R :=
  fun j =>
    operand (args.indexMap (i, houtDims ▸ j))
