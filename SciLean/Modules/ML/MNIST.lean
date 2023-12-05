import SciLean.Core.FloatAsReal
import SciLean.Modules.ML.Dense
import SciLean.Modules.ML.Convolution
import SciLean.Modules.ML.Pool
import SciLean.Modules.ML.Activation
import SciLean.Modules.ML.SoftMax

set_option synthInstance.maxSize 2000

namespace SciLean.ML

open ArrayType

def mnist (w x) := 
  (fun ((w₁,b₁),(w₂,b₂),(w₃,b₃)) (x : Float^[1,28,28]) =>
    x |> conv2d 32 1 w₁ b₁
      |> map gelu
      |> avgPool
      |> dense 100 w₂ b₂
      |> map gelu 
      |> dense 10 w₃ b₃
      |> softMax 1) w x

#generate_revDeriv mnist w x
  prop_by unfold mnist; simp[mnist.match_1]; fprop
  trans_by unfold mnist; simp[mnist.match_1]; ftrans

