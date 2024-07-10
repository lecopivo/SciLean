import SciLean.Core.Rand.PullMean

open SciLean

opaque foo : SciLean.Rand ℝ

example :
  (let a := foo.mean
   let b := (foo + (1:ℝ)).mean
   let x := (2:ℝ)
   let c := (foo + x).mean
   let d := (foo + (3:ℝ)).mean
   a + b + 2*c + d)
  =
  (do
      let x ← foo
      let x_1 ← foo + (1:ℝ)
      let x_2 : ℝ := 2
      let x_3 ← foo + x_2
      let x_4 ← foo + (3:ℝ)
      pure (x + x_1 + 2 * x_3 + x_4)).mean := by conv => lhs; pull_mean

example (y : ℝ) :
  (let x := (2:ℝ)* y
   (foo + x).mean)
  =
  (let x := 2 * y;
   foo + x).mean := by conv => lhs; pull_mean

example (y : ℝ) :
  (let z := y * y
   let x := (foo + y + z).mean
   x + y*x + y + z)
  =
  (let z := y * y;
    do
    let x ← foo + y + z
    pure (x + y * x + y + z)).mean := by conv => lhs; pull_mean

example (y : ℝ) :
  (let x := (foo + y).mean
   x + y*x + y)
  =
  (do
     let x ← foo + y
     pure (x + y * x + y)).mean := by conv => lhs; pull_mean
