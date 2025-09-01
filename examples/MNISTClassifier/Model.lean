 import Lean
-- import SciLean
import SciLean.Core.FloatAsReal
import SciLean.Modules.ML.Dense
import SciLean.Modules.ML.Convolution
import SciLean.Modules.ML.Pool
import SciLean.Modules.ML.Activation

open SciLean
open IO FS System

open NotationOverField
set_default_scalar Float
set_option synthInstance.maxSize 2000

open ML ArrayType in
def model (w x) := 
  (fun ((w₁,b₁),(w₂,b₂),(w₃,b₃)) (x : Float^[1,28,28]) =>
    x |> conv2d 32 1 w₁ b₁
      |> map gelu
      |> avgPool
      |> dense 100 w₂ b₂
      |> map gelu
      |> dense 10 w₃ b₃) w x
      -- |> softMax


#generate_revDeriv model w x
  prop_by unfold model; simp[model.match_1]; fprop
  trans_by unfold model; simp[model.match_1]; ftrans


def batchLoss (w) (images : Float^[1,28,28]^[batchSize]) (labels : Float^[10]^[batchSize]) := 
  ∑ i, ‖(model w images[i] - labels[i])‖₂
