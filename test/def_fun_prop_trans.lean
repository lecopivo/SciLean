import SciLean

open SciLean

variable
  {K : Type} [RCLike K]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]

set_default_scalar K

namespace DefFunPropTransTest

def mul (x y : K) : K := x * y

example : Differentiable K (fun xy : K×K => xy.1 * xy.2) := by fun_prop


def_fun_prop mul in x y
  with_transitive
  arg_subsets
  : Differentiable K


def_fun_trans mul in x y
  arg_subsets
  : revFDeriv K


/--
info: DefFunPropTransTest.mul.arg_xy.Continuous_rule {K : Type} [RCLike K] : Continuous fun xy => mul xy.1 xy.2
-/
#guard_msgs in
#check mul.arg_xy.Continuous_rule

/--
info: DefFunPropTransTest.mul.arg_xy.Differentiable_rule {K : Type} [RCLike K] : Differentiable K fun xy => mul xy.1 xy.2
-/
#guard_msgs in
#check mul.arg_xy.Differentiable_rule


/--
info: DefFunPropTransTest.mul.arg_x.Differentiable_rule {K : Type} [RCLike K] (y : K) : Differentiable K fun x => mul x y
-/
#guard_msgs in
#check mul.arg_x.Differentiable_rule

/--
info: DefFunPropTransTest.mul.arg_y.Differentiable_rule {K : Type} [RCLike K] (x : K) : Differentiable K fun y => mul x y
-/
#guard_msgs in
#check mul.arg_y.Differentiable_rule


/--
info: DefFunPropTransTest.mul.arg_xy.revFDeriv_rule {K : Type} [RCLike K] : <∂ xy, mul xy.1 xy.2 = mul.arg_xy.revFDeriv
-/
#guard_msgs in
#check mul.arg_xy.revFDeriv_rule

/--
info: DefFunPropTransTest.mul.arg_xy.revFDeriv {K : Type} [RCLike K] (x : K × K) : K × (K → K × K)
-/
#guard_msgs in
#check mul.arg_xy.revFDeriv


example :
  (revFDeriv K fun (x : K) => mul x x)
  =
  (fun x =>
      let zdf := mul.arg_xy.revFDeriv (x, x);
      (zdf.1, fun dz =>
        let dy := zdf.2 dz;
        dy.1 + dy.2)) := by fun_trans


def add (x y : X) : X := x + y

def_fun_prop add in x y
  with_transitive
  arg_subsets
  {K} [RCLike K] [NormedSpace K X] : Differentiable K

def_fun_trans add in x y
  arg_subsets
  {K : Type} [RCLike K] [AdjointSpace K X] [CompleteSpace X] : revFDeriv K


/--
info: DefFunPropTransTest.add.arg_xy.Differentiable_rule.{u_1} {X : Type} [NormedAddCommGroup X] {K : Type u_1} [RCLike K]
  [NormedSpace K X] : Differentiable K fun xy => add xy.1 xy.2
-/
#guard_msgs in
#check add.arg_xy.Differentiable_rule

/--
info: DefFunPropTransTest.add.arg_xy.revFDeriv_rule {X : Type} [NormedAddCommGroup X] {K : Type} [RCLike K]
  [AdjointSpace K X] : <∂ xy, add xy.1 xy.2 = add.arg_xy.revFDeriv
-/
#guard_msgs in
#check add.arg_xy.revFDeriv_rule



example :
  (revFDeriv K fun (x : K) =>
    let x1 := mul x x
    let x2 := mul x1 x1
    let x3 := mul x2 x2
    let x4 := mul x3 x3
    let x5 := mul x4 x4
    x5)
  =
  fun x =>
    let zdf := mul.arg_xy.revFDeriv (x, x);
    let ydg := zdf.1;
    let zdf_1 := mul.arg_xy.revFDeriv (ydg, ydg);
    let ydg := zdf_1.1;
    let zdf_2 := mul.arg_xy.revFDeriv (ydg, ydg);
    let ydg := zdf_2.1;
    let zdf_3 := mul.arg_xy.revFDeriv (ydg, ydg);
    let ydg := zdf_3.1;
    let zdf_4 := mul.arg_xy.revFDeriv (ydg, ydg);
    let ydg := zdf_4.1;
    (ydg, fun dz =>
      let dy := zdf_4.2 dz;
      let dy := dy.1 + dy.2;
      let dy := zdf_3.2 dy;
      let dy := dy.1 + dy.2;
      let dy := zdf_2.2 dy;
      let dy := dy.1 + dy.2;
      let dy := zdf_1.2 dy;
      let dy := dy.1 + dy.2;
      let dy := zdf.2 dy;
      dy.1 + dy.2) :=
by
  conv => lhs; lfun_trans

example :
  (revFDeriv K fun (x : K) =>
    let x1 := mul x x
    let x2 := mul x1 (mul x x)
    let x3 := mul x2 (mul x1 x)
    x3)
  =
  fun x =>
    let zdf := mul.arg_xy.revFDeriv (x, x);
    let ydg := zdf.1;
    let zdf_1 := mul.arg_xy.revFDeriv (x, x);
    let zdf_2 := zdf_1.1;
    let zdf_3 := mul.arg_xy.revFDeriv (ydg, zdf_2);
    let ydg_1 := zdf_3.1;
    let zdf_4 := mul.arg_xy.revFDeriv (ydg, x);
    let zdf_5 := zdf_4.1;
    let zdf_6 := mul.arg_xy.revFDeriv (ydg_1, zdf_5);
    let ydg := zdf_6.1;
    (ydg, fun dz =>
      let dy := zdf_6.2 dz;
      let dy_1 := zdf_4.2 dy.2;
      let dxdy := dy_1.2;
      let dxdy_1 := dy_1.1;
      let dxdy_2 := dy.1;
      let dy := zdf_3.2 dxdy_2;
      let dy_2 := zdf_1.2 dy.2;
      let dx := dy_2.1 + dy_2.2;
      let dx_1 := dy.1;
      let dxdy := dxdy + dx;
      let dxdy_3 := dxdy_1 + dx_1;
      let dy := zdf.2 dxdy_3;
      let dx := dy.1 + dy.2;
      dxdy + dx) := by
  conv => lhs; lfun_trans

end DefFunPropTransTest
