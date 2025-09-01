import SciLean

open SciLean


open Scalar

variable (n : ℕ)

/--
info: HasRevFDeriv ℝ
  (fun x =>
    let x := x * x;
    let x := x * exp (exp x);
    x)
  fun x =>
  let ydg₁ := x * x;
  let a := exp ydg₁;
  let a_1 := exp a;
  let ydg₁_1 := ydg₁ * a_1;
  (ydg₁_1, fun dy =>
    let dy₁ := ydg₁ * dy;
    let dy₂ := a_1 * dy;
    let dy := dy₁ * a_1;
    let dx := dy * a;
    let dx := dx + dy₂;
    let dy₁ := x * dx;
    let dy₂ := x * dx;
    let dx := dy₁ + dy₂;
    dx) : Prop
-/
#guard_msgs in
#check (HasRevFDeriv ℝ (fun x : ℝ => Id'.run do
           let mut x := x
           x := x * x
           x := x * exp (exp x)
           return x) _)
  rewrite_by data_synth; lsimp


-- bug in data synth
-- #check (HasRevFDeriv ℝ (fun x : ℝ => Id'.run do
--            let mut x := x
--            x := x * x
--            if n > 10 then
--              x := x * exp (exp x)
--            if n > 20 then
--              x := x * exp (exp x)
--            return x) _) rewrite_by lsimp
