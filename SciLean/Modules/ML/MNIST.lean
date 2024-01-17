import SciLean.Core.FloatAsReal
import SciLean.Modules.ML.Dense
import SciLean.Modules.ML.Convolution
import SciLean.Modules.ML.Pool
import SciLean.Modules.ML.Activation
import SciLean.Modules.ML.SoftMax
import SciLean.Data.Random

set_option synthInstance.maxSize 2000

namespace SciLean.ML

open ArrayType

instance : Inhabited (Idx 10) := ⟨0⟩

def nnet (w x) :=
  (fun ((w₁,b₁),(w₂,b₂),(w₃,b₃)) (x : Float^[1,28,28]) =>
    x |> conv2d 8 1 w₁ b₁
      |> map gelu
      |> avgPool
      |> dense 30 w₂ b₂
      |> map gelu
      |> dense 10 w₃ b₃
      |> softMax 0.1) w x

#generate_revDeriv nnet w
  prop_by unfold nnet; simp[nnet.match_1]; fprop
  trans_by unfold nnet; ftrans


abbrev weightsType (_f : α → β → γ) := α
abbrev inputType (_f : α → β → γ) := β
abbrev outputType (_f : α → β → γ) := γ

def nnet.initWeights := Random.rand (weightsType ML.nnet) |> IO.runRand
