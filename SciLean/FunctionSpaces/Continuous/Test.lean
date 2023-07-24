import SciLean.FunctionSpaces.Continuous.Basic
import SciLean.Profile

set_option profiler true
set_option profiler.threshold 10

example : Continuous (fun x : ℝ => 
  let x1 := x
  let x2 := x + x1
  let x3 := x + x1 + x2
  let x4 := x + x1 + x2 + x3
  let x5 := x + x1 + x2 + x3 + x4
  let x6 := x + x1 + x2 + x3 + x4 + x5
  let x7 := x + x1 + x2 + x3 + x4 + x5 + x6
  x7) := by fprop


example : Continuous (fun x : ℝ => 
  let x1 := x
  let x2 := x + x1
  let x3 := x + x1 + x2
  let x4 := x + x1 + x2 + x3
  let x5 := x + x1 + x2 + x3 + x4
  let x6 := x + x1 + x2 + x3 + x4 + x5
  let x7 := x + x1 + x2 + x3 + x4 + x5 + x6
  x7) := by continuity
