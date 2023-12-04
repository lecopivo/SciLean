import SciLean.Core
import SciLean.Data.DataArray
import SciLean.Data.Prod
import Mathlib

namespace SciLean

variable 
  {R : Type} [RealScalar R] [PlainDataType R]

set_default_scalar R

def conv2d
  {n m: USize} {ι} [Index ι] (filterNum : USize) (r : Int64) 
  (weights : R^[filterNum, [-r:r], [-r:r]]) (bias x : R^[ι,n,m]) : R^[[filterNum,ι],n,m] := 
  ⊞ ((k,l),i,j) => bias[(l,i,j)] + ∑ i' j', weights[(k,i',j')] * x[(l, i'.1 +ᵥ i,j'.1 +ᵥ j)] 

#generate_revDeriv conv2d weights bias x
  prop_by unfold conv2d; fprop
  trans_by unfold conv2d; ftrans

#exit

namespace Mathlib.Meta.NormNum
open Qq Lean Meta

theorem isNat_USizeDiv : {a b : USize} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' → Nat.div (a' % USize.size) (b' % USize.size) = c → IsNat (a / b) c
  | _, _, a', b', _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨sorry⟩

@[norm_num (_ : USize) / (_ : USize)]
def evalUSizeDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q USize := ⟨⟩
  haveI' : $e =Q $a / $b := ⟨⟩
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := USize))
  let sUSize : Q(AddMonoidWithOne USize) := q(inferInstance)
  let ⟨na, pa⟩ ← deriveNat a sUSize; let ⟨nb, pb⟩ ← deriveNat b sUSize
  have nc : Q(ℕ) := mkRawNatLit ((na.natLit! % USize.size) / (nb.natLit! % USize.size))
  have pf : Q(Nat.div ($na % USize.size) ($nb % USize.size) = $nc) := (q(Eq.refl $nc) : Expr)
  return .isNat sUSize nc q(isNat_USizeDiv $pa $pb $pf)

end Mathlib.Meta.NormNum

syntax (name:=deduceBy) "deduce_by " conv : tactic -- => `(tactic| (trace_state; sorry))

open Lean Meta Elab Tactic Qq
@[tactic deduceBy]  
partial def deduceByTactic : Tactic
| `(tactic| deduce_by $t:conv) => do

  let goal ← getMainGoal
  let .some (_,lhs,rhs) := Expr.eq? (← goal.getType) | throwError "expected `?m = e`, got {← ppExpr (← goal.getType)}"

  if ¬lhs.isMVar then
    throwError "lhs is not mvar"

  -- TODO: support that rhs can be mvar too
  let (a,b) := (lhs,rhs)
  -- now we assume that a is mvar and be

  let (b',prf) ← elabConvRewrite b t

  a.mvarId!.assign b'
  goal.assign prf
| _ => throwUnsupportedSyntax

def toIdx' {ι} [Index ι] {k : USize} (i : ι) (h : (k = Index.size ι) := by deduce_by (simp; ring_nf; norm_num)) : Idx k := h ▸ (toIdx i)

@[simp]
theorem hii (n) : Index.size (Idx n) = n := by rfl

@[simp]
theorem hoo {ι κ} [Index ι] [Index κ] : Index.size (ι × κ) = Index.size ι * Index.size κ := by sorry_proof

variable (n : USize) (i : Idx 5 × Idx 10 × Idx n)

#check toIdx' i
  
-- syntax (name:=bar) "bar" : tactic
syntax (name:=bar) "norm_index" : tactic -- => `(tactic| (trace_state; sorry))

open Lean Meta Elab Tactic Qq
@[tactic bar]  
partial def barTactic : Tactic := fun _ => do

  let goal ← getMainGoal
  IO.println s!"main goal {← goal.getType >>= ppExpr |> liftM}"
  let .some (_,lhs,rhs) := Expr.eq? (← goal.getType) | throwError "expected `f(?k) = n`"

  if ¬lhs.hasMVar && ¬rhs.hasMVar then
    throwError "expected `f(?k) = n`"

  let rec go (k n : Q(USize)) : MetaM (Expr×Expr) := do
    let (k,n) := if k.hasMVar then (k,n) else (n,k)
    if k.isMVar then
      return (k,n)
    else
      match k with
      | ~q($a * $b) => 
        match a.hasMVar, b.hasMVar with
        | true, false => go a q($n / $b)
        | false, true => go b q($n / $a)
        | _, _ => throwError "norm_index: unexpected operation `{← ppExpr k}` in expression {← goal.getType >>= ppExpr}"
      | _ => throwError "norm_index: unexpected operation `{← ppExpr k}` in expression {← goal.getType >>= ppExpr}"
  
  
  let (a,b) ← go lhs rhs
  let (a',prf) ← elabConvRewrite b (← `(conv| norm_num)) 

  a.mvarId!.assign a'
  IO.println s!"simplified rhs {← (ppExpr b |> liftM)}"
  IO.println s!"simplified rhs {← (ppExpr a' |> liftM)}"

  let _ ← goal.instantiateMVarsInType
  -- let _ ← goal.instantiateMVars
  IO.println s!"new goal is {← goal.getType >>= ppExpr |> liftM}"
  let subgoals ← evalTacticAt (← `(tactic| norm_num)) goal

  if subgoals.length ≠ 0 then
    throwError "norm_index: failed to show {← goal.getType >>= ppExpr |> liftM}"

  goal.assign (← mkEqSymm prf)
  
  pure ()

/-- Splits index `i : Idx (n*m)` into `(i / n, i % n)`-/
def Idx.prodSplit (i : Idx (n*m)) : Idx n × Idx m := 
  (⟨i.1 / n, sorry_proof⟩, ⟨i.1 % n, sorry_proof⟩)

/-- Splits index `i : Idx (n*m)` into `(i / m, i % m)`-/
def Idx.prodSplit' (i : Idx (n*m)) : Idx m × Idx n := 
  (⟨i.1 % m, sorry_proof⟩, ⟨i.1 / m, sorry_proof⟩)

#eval toIdx ((2 : Idx 3), (5 : Idx 10))

def foo (i : Idx n) {k : USize} (h : n = 2*k := by norm_index) : Idx k := 
  (h▸i).prodSplit'.1



#exit

-- set_option pp.all true in
#check foo (5 : Idx 10)


example : (15 : Fin 10) = (5 : Fin 10) := by decide
example : (15 : Fin 10) = (5 : Fin 10) := by native_decide
example : (18446744073709552000 : Fin USize.size) = (384 : Fin USize.size) := by decide -- failed to reduce to 'true'
example : (18446744073709552000 : Fin USize.size) = (384 : Fin USize.size) := by native_decide 


#check USize

#check ( ((7 : Fin 10)/2) rewrite_by norm_num)

#check ( (10/2) rewrite_by norm_num)



theorem usize_eq (a b : USize) (n m : Nat) (ha : n.toUSize = a) (hb : m.toUSize = b)
  



example : ((18446744073709552000 : USize) = (384 : USize)) := by norm_num
example : ((100/2 : USize) = (384 : USize)) := by norm_num

example : (( : USize) = (384 : USize)) := by norm_num


#check reduceNat


variable (n k : ℕ) 

#check ((3 * n + 3  + 21 + n) / 2) rewrite_by norm_num;ring_nf

end SciLean
/- 20 / 5 -/
#norm_num (20 : USize) / (5 : USize)


/- 4 -/
#norm_num (20 : USize) / (5 : USize)
/- 5 -/
#norm_num ((10:USize)*(2:USize) / 4 : USize)


variable (n k : USize)

#check (3 * k + 10 - 4 * n + 20 - n - 5) rewrite_by ring_nf


#check Lean.Meta.reduceNatNative


