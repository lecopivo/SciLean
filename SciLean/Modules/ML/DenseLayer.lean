import SciLean
-- import SciLean.Data.DataArray
-- import SciLean.Data.Prod
-- import SciLean.Util.Profile

namespace SciLean


variable 
  -- {R : Type _} [RealScalar R]
  {K : Type _} [IsROrC K]
  {W : Type _} [Vec K W]

set_default_scalar K

variable {α β κ ι : Type} [Index α] [Index κ] [Index β] [Index ι] [PlainDataType K] [PlainDataType R]

variable (κ)
def denseLazy (weights : κ → ι → K) (bias : κ → K) (x : ι → K) (j : κ) : K := 
  ∑ i, weights j i * x i + bias j
variable {κ}


#generate_revCDeriv denseLazy weights bias x
  prop_by unfold denseLazy; fprop
  trans_by unfold denseLazy; ftrans

#generate_revCDeriv denseLazy weights bias x | j
  prop_by unfold denseLazy; fprop
  trans_by unfold denseLazy; ftrans; simp (config := {zeta:=false}) only [curryN,uncurryN, CurryN.curry, UncurryN.uncurry]; ftrans 

attribute [ftrans] denseLazy.arg_weightsbiasx_j.revCDeriv_rule_def
-- attribute [ftrans] denseLazy.arg_weightsbiasx.revCDeriv_rule_def

variable (κ)
def dense (weights : DataArrayN K (κ×ι)) (bias : K^κ) (x : K^ι) : K^κ := 
  -- ⊞ j => ∑ i, weights[(j,i)] * x[i] + bias[j]
  ⊞ j => denseLazy κ (fun j i => weights[(j,i)]) (fun j => bias[j]) (fun i => x[i]) j
variable {κ}
set_option pp.funBinderTypes true in
-- set_option trace.Meta.Tactic.fprop.unify true in
-- set_option trace.Meta.Tactic.fprop.discharge true in
-- set_option trace.Meta.Tactic.fprop.step true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.ftrans.step true in
#generate_revCDeriv dense weights bias x
  prop_by unfold dense; fprop
  trans_by unfold dense; ftrans; ftrans only


#eval 0


#check denseLazy.arg_weightsbiasx_j.revCDeriv

set_option trace.Meta.Tactic.ftrans.step true
set_option trace.Meta.Tactic.ftrans.theorems true
set_option trace.Meta.Tactic.fprop.discharge true
set_option trace.Meta.Tactic.simp.discharge true
set_option trace.Meta.Tactic.simp.congr true
set_option trace.Meta.Tactic.simp.rewrite true
set_option trace.Meta.Tactic.simp.unify true
example [SemiInnerProductSpace K W]
  : <∂ (fun (x : ((W × DataArrayN K (κ × ι)) × K ^ κ) × K ^ ι) (j : κ) =>
        denseLazy κ (fun (j : κ) (i : ι) => x.fst.fst.snd[(j, i)]) (fun (j : κ) => x.fst.snd[j]) (fun (i : ι) => x.snd[i]) j)
    =
    fun _ => 0 := 
by
  conv => 
    lhs
    ftrans only


#check SciLean.denseLazy.arg_weightsbiasx_j.revCDeriv_rule_def
#check SciLean.denseLazy.arg_weightsbiasx_j.revCDeriv_rule
#check SciLean.denseLazy.arg_weightsbiasx_j.HasAdjDiff_rule

#exit
variable {W : Type _} [SemiInnerProductSpace K W]

example (x : W → DataArrayN K ι) (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i]))
  : HasAdjDiff K x := by fprop

example (x : W → DataArrayN K ι) (i : ι) (hx : HasAdjDiff K x)
  : HasAdjDiff K fun w => (x w)[i] := by fprop

example (x : W → DataArrayN K ι) (hx : HasAdjDiff K x)
  : HasAdjDiff K fun w i => (x w)[i] := by fprop


-- def foo : Float → DataArrayN Float (Idx 10) := sorry

-- -- set_option maxHeartbeats 10000

-- -- set_option trace.Meta.isDefEq true in
-- open Lean Meta Qq in
-- #eval show MetaM Unit from do

--   let X : Q(Type) := q(Float → DataArrayN Float (Idx 10))
--   withLocalDecl `x default X fun x => do
--   let x : Q($X) := x
--   let HX := q(IsDifferentiable Float $x)
--   withLocalDecl `hx default HX fun hx => do

--   let H := q(IsDifferentiable Float fun w => ⊞ i => ($x w)[i])
--   let h ← mkFreshExprMVar H 
--   IO.println (← isDefEq hx h)



-- set_option trace.Meta.isDefEq true in
-- open Lean Meta Qq in
-- #eval show MetaM Unit from do

--   let X : Q(Type) := q(Float → DataArrayN Float (Idx 10))
--   withLocalDecl `x default X fun x => do
--   let x : Q($X) := x
--   let HX := q(IsDifferentiable Float $x)
--   withLocalDecl `hx default HX fun hx => do

--   let H := q(IsDifferentiable Float fun w => ⊞ i => ($x w)[i])
--   let h ← mkFreshExprMVar H 
--   IO.println (← isDefEq hx h)

-- set_option maxHeartbeats 50000

  
-- set_option trace.Meta.Tactic.fprop.step true in 
-- set_option trace.Meta.Tactic.fprop.unify true in
-- set_option trace.Meta.Tactic.fprop.discharge true in

example 
  (x : Float → DataArrayN Float (Idx 10)) (hx : IsDifferentiable Float x)
  : IsDifferentiable Float (fun w => ⊞ i => (x w)[i]) := 
by
  fprop


variable (x : Float → DataArrayN Float (Idx 10)) (hx : ∀ i : Idx 10, HasAdjDiff Float (fun w => (x w)[i]))

set_default_scalar Float

#check <∂ w, x w


example 
  : (<∂ w, ∑ i, (x w)[i])
    =
    fun w => 
      let xdx := <∂ sorry :=
by
  sorry

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.rewrite true in
#check 
  <∂ w, ∑ i, (x w)[i]
  rewrite_by
    simp (config := {zeta := false}) only [SciLean.EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta := false}) only [SciLean.revCDeriv.pi_rule _ _ sorry]
    

    simp (config := {zeta := false}) only
    ftrans only



@[fprop]
theorem dense.arg_weightsbiasx.IsDifferentiable_rule 
  (weights : W → DataArrayN K (κ×ι)) (bias : W → DataArrayN K κ) (x : W → DataArrayN K ι)
  (hweights : IsDifferentiable K weights) (hbias : IsDifferentiable K bias) (hx : IsDifferentiable K x)
  : IsDifferentiable K fun w => dense κ (weights w) (bias w) (x w) :=
by
  unfold dense; unfold denseLazy
  fprop


@[ftrans]
theorem dense.arg_weightsbiasx.fwdCDeriv_rule
  (weights : W → DataArrayN K (κ×ι)) (bias : W → DataArrayN K κ) (x : W → DataArrayN K ι)
  (hweights : IsDifferentiable K weights) (hbias : IsDifferentiable K bias) (hx : IsDifferentiable K x)
  : (fwdCDeriv K fun w => dense κ (weights w) (bias w) (x w) )
    =
    ((fwdCDeriv K fun w => dense κ (weights w) (bias w) (x w))
     rewrite_by unfold dense; unfold denseLazy; autodiff) := 
by
  unfold dense; unfold denseLazy
  conv => lhs; autodiff
  

set_option trace.Meta.Tactic.ftrans.step true in
@[ftrans]
theorem dense.arg_weightsbiasx.revCDeriv_rule  {W : Type} [SemiInnerProductSpace K W]
  (weights : W → DataArrayN K (κ×ι)) (bias : W → DataArrayN K κ) (x : W → DataArrayN K ι)
  (hweights : HasAdjDiff K weights) (hbias : HasAdjDiff K bias) (hx : HasAdjDiff K x)
  : (revCDeriv K fun w => dense κ (weights w) (bias w) (x w) )
    =
    ((revCDeriv K fun w => dense κ (weights w) (bias w) (x w))
     rewrite_by unfold dense; unfold denseLazy; autodiff; autodiff) := 
by
  sorry


#exit
section denseDerivTest
  variable (weights : DataArrayN R (κ×ι)) (bias : DataArrayN R κ) (x : DataArrayN R ι)

  #check 
    ∇ x, dense κ weights bias x
    rewrite_by
      unfold dense; symdiff

  #check 
    ∇ bias, dense κ weights bias x
    rewrite_by
      unfold dense; symdiff

  #check 
    ∇ weights, dense κ weights bias x
    rewrite_by
      unfold dense; symdiff

end denseDerivTest


