import SciLean


-- there are some linker issues :(
#exit

open SciLean


variable (R : Type) [RealScalar R]

set_default_scalar R


/--
info: fun x =>
  let zdz := x * x;
  let ydy := zdz ^ 3;
  let ydy := ydy + ydy;
  fun dx =>
  let zdz_1 := x * dx + dx * x;
  let ydy_1 := 3 * zdz_1 * zdz ^ 2;
  let ydy_2 := ydy_1 + ydy_1;
  (ydy, ydy_2) : R → R → R × R
-/
#guard_msgs in
#check (∂> (x : R), Id'.run do
         let mut x := x
         x := x*x
         x := x^3
         x := x+x
         return x) rewrite_by autodiff


variable (a b : R)


#check (fwdFDeriv R fun x : R => Id'.run do
         let mut x := x
         if h : a < b then
           x := x^3
         if 0 < b then
           x := x^4
         if 0 < a then
           x := x^5
         return x) rewrite_by
  fun_trans (config:={zeta:=false}) only [simp_core]
  let_normalize (config:={removeLambdaLet:=false,removeNoFVarLet:=true})
  fun_trans (config:={zeta:=false}) only [simp_core]
  lsimp (config:={singlePass:=true})
  lsimp (config:={singlePass:=true})


#check (fwdFDeriv R (fun x : R =>
       let f := fun y : R => y
       f x)) rewrite_by fun_trans (config:={zeta:=false}) -- nothing happens :(


set_option linter.unusedTactic false
example : Differentiable R ((fun x : R =>
       let f := fun y : R => y + x
       f x)) := by (try fun_prop); sorry_proof -- fun_prop does not work :(


-- #check (fwdFDeriv R fun x : R => Id'.run do
--          let mut x := x
--          x := x^2
--          if a < b then
--            x := x^3
--          if 0 < b then
--            x := x^4
--          if 0 < a then
--            x := x^5
--          return x) rewrite_by autodiff (disch:=simp only [simp_core])

-- #guard_msgs in
-- #check (<∂ (x : R), Id'.run do
--          let mut x := x
--          x := x*x
--          x := x^3
--          x := x+x
--          return x) rewrite_by autodiff
