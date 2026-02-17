import SciLean.Probability.PullMean
import SciLean.Util.RewriteBy

open SciLean Rand


variable {X : Type} [MeasurableSpace X] [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  (x' y' : Rand X)


/--
info: (do
    let x ← x'
    let y : X := y'.mean
    pure (x + y)).mean : X
-/
#guard_msgs in
#check
  (let x := x'.mean
   let y := y'.mean
   x + y)
  rewrite_by pull_mean
