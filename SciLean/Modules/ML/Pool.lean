import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod
import SciLean.Core.Meta.GenerateRevCDeriv'

import SciLean.Core.FloatAsReal
import SciLean.Core.Function

namespace SciLean

variable 
  {R : Type} [RealScalar R]

set_default_scalar R

variable {κ ι κ'} [Index κ] [Index κ'] [Index ι] [PlainDataType R]


example
  {ι X : Type} [Index ι]
  [SemiInnerProductSpace R X]
  (f : ι → X) (op : X → X → X) (hop : HasAdjDiff R fun (a,a') => op a a')
  (a : Nat)
  : HasAdjDiffM (m:=Id) R fun (xy : (ι → X)×X) =>
          ForInStep.yield
            (op xy.2
              (xy.1 (SciLean.fromIdx ⟨a.toUSize, sorry_proof⟩))) := 
by
  set_option trace.Meta.Tactic.fprop.discharge true in
  set_option trace.Meta.Tactic.fprop.unify true in
  set_option trace.Meta.Tactic.fprop.step true in
  fprop


set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.ftrans.step true in
def Index.joinlM.arg_f.revCDeriv {ι X : Type} [Index ι] 
  [SemiInnerProductSpace R X]
  (f : ι → X) (op : X → X → X) (hop : HasAdjDiff R fun (a,a') => op a a')
  : X × (X → (ι→X)) :=
  (<∂ (f':=f), Index.joinl f' op)
  rewrite_by 
    unfold Index.joinl
    ftrans only
    ftrans only
    simp
    ftrans only
    ftrans only
    simp (config := {zeta:=false})


variable {X : Type} [SemiInnerProductSpace R X] (a : X → X) (ha : HasAdjDiff R a)
attribute [simp] Id.run.arg_x.revCDeriv_rule

#check Lean.Expr.modArg

variable (c : R)

#check 
  (revDerivM (m:=Id) R (fun x : R => (0 : R)))
  rewrite_by
    ftrans


set_option trace.Meta.Tactic.simp.unify true in
    -- ftrans

#exit
#check 
  (revDerivM (m:=Id) R (fun x : R => pure (default : R)))
  rewrite_by
    ftrans
    simp 

variable (κ) 
/-- 
  @param α indexing set of 
  -/
def poolLazy
  (indexSplit : ι ≃ κ×κ') 
  (op : R → R → R)
  (x : ι → R)
  (j : κ) : R := 
  Function.reduce (fun j' : κ' => x (indexSplit.symm (j,j'))) op

variable {κ}

#generate_revCDeriv' poolLazy x | j
  prop_by unfold poolLazy; fprop
  trans_by unfold poolLazy; ftrans
