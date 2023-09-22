import SciLean.Core

open Lean SciLean

set_option linter.unusedVariables false 

def mymul {K : Type u} [instK : IsROrC K] (x y : K) := x * y

#generate_revCDeriv mymul x y by unfold mymul; autodiff
#generate_revCDeriv mymul x by unfold mymul; autodiff
#generate_revCDeriv mymul y by unfold mymul; autodiff

#generate_fwdCDeriv mymul x y 
  prop_by unfold mymul; fprop
  trans_by unfold mymul; autodiff

#generate_fwdCDeriv mymul x
  prop_by unfold mymul; fprop
  trans_by unfold mymul; autodiff

#generate_fwdCDeriv mymul y
  prop_by unfold mymul; fprop
  trans_by unfold mymul; autodiff


/--
info: mymul.arg_x.revCDeriv.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [instW : SemiInnerProductSpace K W] (x y : K)
  (dx' : K → W) : K × (K → W)
-/
#guard_msgs in
#check mymul.arg_x.revCDeriv

/--
info: mymul.arg_xy.revCDeriv.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [instW : SemiInnerProductSpace K W] (x y : K)
  (dx' dy' : K → W) : K × (K → W)
-/
#guard_msgs in
#check mymul.arg_xy.revCDeriv

/--
info: mymul.arg_y.revCDeriv_rule_def.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [instW : SemiInnerProductSpace K W]
  (x : K) (y : W → K) (hy : HasAdjDiff K y) :
  (<∂ w,
      let y := y w;
      mymul x y) =
    fun w =>
    let y := <∂ y w;
    mymul.arg_y.revCDeriv x y.fst y.snd
-/
#guard_msgs in
#check mymul.arg_y.revCDeriv_rule_def


/--
info: mymul.arg_xy.revCDeriv_rule_def.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [instW : SemiInnerProductSpace K W]
  (x y : W → K) (hx : HasAdjDiff K x) (hy : HasAdjDiff K y) :
  (<∂ w,
      let x := x w;
      let y := y w;
      mymul x y) =
    fun w =>
    let x := <∂ x w;
    let y := <∂ y w;
    mymul.arg_xy.revCDeriv x.fst y.fst x.snd y.snd
-/
#guard_msgs in
#check mymul.arg_xy.revCDeriv_rule_def


/--
info: mymul.arg_xy.fwdCDeriv_rule_def.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : Vec K W] (x y : W → K)
  (hx : IsDifferentiable K x) (hy : IsDifferentiable K y) :
  ∂> w, mymul (x w) (y w) = fun w dw =>
    let xdx := ∂> x w dw;
    let ydy := ∂> y w dw;
    mymul.arg_xy.fwdCDeriv xdx.fst ydy.fst xdx.snd ydy.snd
-/
#guard_msgs in
#check mymul.arg_xy.fwdCDeriv_rule_def


/--
info: mymul.arg_xy.IsDifferentiable_rule.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : Vec K W] (x y : W → K)
  (hx : IsDifferentiable K x) (hy : IsDifferentiable K y) : IsDifferentiable K fun w => mymul (x w) (y w)
-/
#guard_msgs in
#check mymul.arg_xy.IsDifferentiable_rule


variable
  {K : Type u} [RealScalar K]
  {ι : Type v} {κ : Type v'} [EnumType ι] [EnumType κ]

set_default_scalar K

def matmul  (A : ι → κ → K) (x : κ → K) (i : ι) : K := ∑ j, A i j * x j

#generate_revCDeriv matmul A x by unfold matmul; autodiff; autodiff
#generate_revCDeriv matmul A | i by unfold matmul; autodiff; autodiff
#generate_revCDeriv matmul x | i by unfold matmul; autodiff; autodiff

#generate_HasAdjDiff matmul A x by unfold matmul; fprop
#generate_HasAdjDiff matmul A x | i by unfold matmul; fprop
#generate_HasAdjDiff matmul A | i by unfold matmul; fprop

-- need to fix ftrans for this to work
-- #generate_revCDeriv matmul A x | i by unfold matmul; autodiff; autodiff
 
