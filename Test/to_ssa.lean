import SciLean.Lean.ToSSA
import SciLean.Util.RewriteBy




/--
info: fun x =>
  let a := x * x;
  a * x : Nat → Nat
-/
#guard_msgs in
#check (fun x : Nat => x*x*x) rewrite_by to_ssa


/--
info: fun x =>
  let a := x * x;
  a * a : Nat → Nat
-/
#guard_msgs in
#check (fun x : Nat => (x*x)*(x*x)) rewrite_by to_ssa


/--
info: fun x =>
  let a := x * x;
  let a := a * a;
  a * a : Nat → Nat
-/
#guard_msgs in
#check (fun x : Nat => ((x*x)*(x*x))*((x*x)*(x*x))) rewrite_by to_ssa


/--
info: fun x =>
  let a := x * x;
  a * a : Nat → Nat
-/
#guard_msgs in
#check (fun x : Nat =>
   let a := x * x
   a * (x * x)) rewrite_by to_ssa


/--
info: fun x =>
  let a := x * x;
  a * a : Nat → Nat
-/
#guard_msgs in
#check (fun x : Nat =>
   let a := x * x
   let b := x * x
   a * b) rewrite_by to_ssa


/--
info: fun x =>
  let c := x * x;
  let a := c * c;
  a * c : Nat → Nat
-/
#guard_msgs in
#check (fun x : Nat =>
   let a :=
     let c := x * x
     (x * x) * c
   let b := x * x
   a * b) rewrite_by to_ssa

/--
info: fun x dx =>
  let a := x.succ;
  let a_1 := dx * a;
  (a, a_1) : Nat → Nat → Nat × Nat
-/
#guard_msgs in
#check (fun x dx : Nat => (x.succ, dx * x.succ)) rewrite_by to_ssa
