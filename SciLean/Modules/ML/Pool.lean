import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod
import SciLean.Core.Meta.GenerateRevCDeriv'

import SciLean.Core.FloatAsReal


namespace SciLean

variable 
  {R : Type} [RealScalar R]

set_default_scalar R

variable {κ ι κ'} [Index κ] [Index κ'] [Index ι] [PlainDataType R]

def _root_.Function.reduce {ι α} [Index ι] [Inhabited α] (f : ι → α) (op : α → α → α) : α := Id.run do
  let n := Index.size ι
  if 0 = n then
    return default
  else
    let mut a ← f (fromIdx ⟨0, sorry_proof⟩)
    for i in [1:n.toNat] do
       a ← op a (← f (fromIdx ⟨i.toUSize, sorry_proof⟩))
    return a

theorem _root_.Function.reducte.arg_f.revCDeriv {ι K X} [Index ι] [IsROrC K] [SemiInnerProductSpace K X]
  (f : ι → X) (dop : X → X×X) : X × (X → (ι→X)) := Id.run do
  let n := Index.size ι
  if 0 = n then
    return (default, 0)
  let mut  a : Array X := Array.mkEmpty n.toNat
  let mut da : Array X := Array.mkEmpty n.toNat
  
  sorry

#eval (fun i : Idx 5 => i.1).reduce (·+·)

#check ForInStep.yield

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
  Index.joinl (fun j' : κ' => x (indexSplit.symm (j,j'))) op

variable {κ}
