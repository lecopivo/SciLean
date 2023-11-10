import SciLean.Core

open Lean SciLean

set_option linter.unusedVariables false 

def mymul {K : Type u} [instK : IsROrC K] (x y : K) := x * y

#generate_revCDeriv mymul x y 
  prop_by unfold mymul; fprop
  trans_by unfold mymul; autodiff

#generate_revCDeriv mymul x
  prop_by unfold mymul; fprop
  trans_by unfold mymul; autodiff

#generate_revCDeriv mymul y 
  prop_by unfold mymul; fprop
  trans_by unfold mymul; autodiff

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
info: mymul.arg_x.revCDeriv.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : SemiInnerProductSpace K W] (x y : K)
  (dx' : K → W) : K × (K → W)
-/
#guard_msgs in
#check mymul.arg_x.revCDeriv

/--
info: mymul.arg_xy.revCDeriv.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : SemiInnerProductSpace K W]
  (x y : K) (dx' dy' : K → W) : K × (K → W)
-/
#guard_msgs in
#check mymul.arg_xy.revCDeriv

/--
info: mymul.arg_y.revCDeriv_rule_def.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : SemiInnerProductSpace K W]
  (x : K) (y : W → K) (hy : HasAdjDiff K y) :
  <∂ w, mymul x (y w) = fun w =>
    let ydy' := <∂ y w;
    mymul.arg_y.revCDeriv x ydy'.1 ydy'.2
-/
#guard_msgs in
#check mymul.arg_y.revCDeriv_rule_def


/--
info: mymul.arg_xy.revCDeriv_rule_def.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : SemiInnerProductSpace K W]
  (x y : W → K) (hx : HasAdjDiff K x) (hy : HasAdjDiff K y) :
  <∂ w, mymul (x w) (y w) = fun w =>
    let xdx' := <∂ x w;
    let ydy' := <∂ y w;
    mymul.arg_xy.revCDeriv xdx'.1 ydy'.1 xdx'.2 ydy'.2
-/
#guard_msgs in
#check mymul.arg_xy.revCDeriv_rule_def


/--
info: mymul.arg_xy.fwdCDeriv_rule_def.{w, u} {K : Type u} [instK : IsROrC K] {W : Type w} [inst_0 : Vec K W] (x y : W → K)
  (hx : IsDifferentiable K x) (hy : IsDifferentiable K y) :
  ∂> w, mymul (x w) (y w) = fun w dw =>
    let xdx := ∂> x w dw;
    let ydy := ∂> y w dw;
    mymul.arg_xy.fwdCDeriv xdx.1 ydy.1 xdx.2 ydy.2
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
  {X : Type v} [SemiInnerProductSpace K X]
  {ι : Type} {κ : Type} [EnumType ι] [EnumType κ]

set_default_scalar K

def matmul  (A : ι → κ → K) (x : κ → K) (i : ι) : K := ∑ j, A i j * x j

#generate_revCDeriv matmul A x 
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff

#generate_revCDeriv matmul A x | i
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff

#generate_revCDeriv matmul A | i 
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff; autodiff

#generate_revCDeriv matmul x | i 
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff; autodiff
  
#generate_fwdCDeriv matmul A x
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff; autodiff

#generate_fwdCDeriv matmul A 
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff; autodiff

#generate_fwdCDeriv matmul x
  prop_by unfold matmul; fprop
  trans_by unfold matmul; autodiff; autodiff
 

-- TODO: make this work even if there is no `[IsROrC K]` in the type signature
-- in this case it will just say that `K` and `α` are vector spaces over some new 
-- field `R` with `[IsROrC R]`
def pairWithScalar {K α ι : Type _} [IsROrC K]
  (r : K) (x : α) := (r,x)

#generate_fwdCDeriv pairWithScalar r x
  prop_by unfold pairWithScalar; fprop
  trans_by unfold pairWithScalar; autodiff
