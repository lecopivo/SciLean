import SciLean.Core

open Lean SciLean

set_option linter.unusedVariables false 

def mymul {K : Type u} [instK : IsROrC K] (x y : K) := x * y

#generate_revCDeriv mymul 2 3 by unfold mymul; autodiff
#generate_revCDeriv mymul 2 by unfold mymul; autodiff
#generate_revCDeriv mymul 3 by unfold mymul; autodiff


/--
info: mymul.arg_x.revCDeriv.{v, u} {K : Type u} [instK : IsROrC K] {W : Type v} [instW : SemiInnerProductSpace K W]
  (xdx : K × (K → W)) (y : K) : K × (K → W)
-/
#guard_msgs in
#check mymul.arg_x.revCDeriv

/--
info: mymul.arg_xy.revCDeriv.{v, u} {K : Type u} [instK : IsROrC K] {W : Type v} [instW : SemiInnerProductSpace K W]
  (xdx ydy : K × (K → W)) : K × (K → W)
-/
#guard_msgs in
#check mymul.arg_xy.revCDeriv

/--
info: mymul.arg_y.revCDeriv_rule_def.{v, u} {K : Type u} [instK : IsROrC K] {W : Type v} [instW : SemiInnerProductSpace K W]
  (x : K) (y : W → K) (hy : HasAdjDiff K y) :
  (<∂ w,
      let y := y w;
      mymul x y) =
    fun w =>
    let y := <∂ y w;
    mymul.arg_y.revCDeriv x y
-/
#guard_msgs in
#check mymul.arg_y.revCDeriv_rule_def


/--
info: mymul.arg_xy.revCDeriv_rule_def.{v, u} {K : Type u} [instK : IsROrC K] {W : Type v} [instW : SemiInnerProductSpace K W]
  (x y : W → K) (hx : HasAdjDiff K x) (hy : HasAdjDiff K y) :
  (<∂ w,
      let x := x w;
      let y := y w;
      mymul x y) =
    fun w =>
    let x := <∂ x w;
    let y := <∂ y w;
    mymul.arg_xy.revCDeriv x y
-/
#guard_msgs in
#check mymul.arg_xy.revCDeriv_rule_def


