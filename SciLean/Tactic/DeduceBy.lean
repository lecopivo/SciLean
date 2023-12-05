import Lean
import Qq

import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Data.UInt
import Mathlib.Tactic.Ring

import SciLean.Util.RewriteBy
import SciLean.Data.Index

/- 
This norm num extension is by Kyle Miller
source: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/norm_num.20for.20USize/near/405939157
-/
namespace Mathlib.Meta.NormNum
open Qq Lean Meta

@[simp]
theorem succ_pow_numBits :
    Nat.succ (2 ^ System.Platform.numBits - 1) = 2 ^ System.Platform.numBits := by
  obtain (hbits | hbits) := System.Platform.numBits_eq <;> norm_num [hbits]

theorem isNat_USizeDiv : {a b : USize} → {a' b' c : ℕ} →
    IsNat a a' → IsNat b b' →
    Nat.div (a' % 2^32) (b' % 2^32) = c →
    Nat.div (a' % 2^64) (b' % 2^64) = c →
    IsNat (a / b) c
  | _, _, a', b', _, ⟨rfl⟩, ⟨rfl⟩, h32, h64 => by
    constructor
    unfold_projs
    unfold USize.div
    unfold_projs
    unfold Fin.div
    unfold_projs
    simp [USize.size]
    obtain (hbits | hbits) := System.Platform.numBits_eq
     <;> · simp [hbits, *]
           generalize_proofs h
           apply USize.eq_of_val_eq
           ext; rename_i x; change x = (x : Fin USize.size)
           rw [Fin.val_cast_of_lt h]

@[norm_num (_ : USize) / (_ : USize)]
def evalUSizeDiv : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q($α))) (b : Q($α)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q USize := ⟨⟩
  haveI' : $e =Q $a / $b := ⟨⟩
  guard <|← withNewMCtxDepth <| isDefEq f q(HDiv.hDiv (α := USize))
  let sUSize : Q(AddMonoidWithOne USize) := q(inferInstance)
  let ⟨na, pa⟩ ← deriveNat a sUSize; let ⟨nb, pb⟩ ← deriveNat b sUSize
  have nc32 : Q(ℕ) := mkRawNatLit ((na.natLit! % 2^32) / (nb.natLit! % 2^32))
  have nc64 : Q(ℕ) := mkRawNatLit ((na.natLit! % 2^64) / (nb.natLit! % 2^64))
  guard <| nc32 == nc64
  haveI' : $nc32 =Q $nc64 := ⟨⟩
  have pf32 : Q(Nat.div ($na % 2 ^ 32) ($nb % 2 ^ 32) = $nc32) := (q(Eq.refl $nc32) : Expr)
  have pf64 : Q(Nat.div ($na % 2 ^ 64) ($nb % 2 ^ 64) = $nc64) := (q(Eq.refl $nc64) : Expr)
  haveI' : Nat.div ($na % 2 ^ 64) ($nb % 2 ^ 64) =Q $nc64 := ⟨⟩
  return .isNat sUSize nc64 q(isNat_USizeDiv $pa $pb $pf32 $pf64)

end Mathlib.Meta.NormNum


namespace SciLean

syntax (name:=deduceBy) "deduce_by " conv : tactic

namespace DeduceBy
open Qq Lean Meta

/-- 
Assuming that `a` has mvar `m` and `b` is an expression.

Return mvar `m` and value `x` for it such that `a=b` is likely to hold.

Examples:
- `a = 4 * ?m + 2`, `b = 2*n` => `(?m, (2*n-2)/4)`
-/
partial def invertNat (a b : Q(Nat)) : MetaM (Q(Nat) × Q(Nat)) := do
  if a.isMVar then 
    return (a,b)
  else
    match a with
    | ~q($x * $y) => 
      if x.hasMVar 
      then invertNat x q($b / $y)
      else invertNat y q($b / $x)
    | ~q($x / $y) => 
      if x.hasMVar 
      then invertNat x q($b * $y)
      else invertNat y q($x / $b)
    | ~q($x + $y) => 
      if x.hasMVar 
      then invertNat x q($b - $y)
      else invertNat y q($b - $x)
    | ~q($x - $y) => 
      if x.hasMVar 
      then invertNat x q($b + $y)
      else invertNat y q($x - $b)
    | _ => 
      throwError s!"`decuce_by` does not support Nat operation {← ppExpr a}"

/-- 
Assuming that `a` has mvar `m` and `b` is an expression.

Return mvar `m` and value `x` for it such that `a=b` is likely to hold.

Examples:
- `a = 4 * ?m + 2`, `b = 2*n` => `(?m, (2*n-2)/4)`
-/
partial def invertUSize (a b : Q(USize)) : MetaM (Q(USize) × Q(USize)) := do
  if a.isMVar then 
    return (a,b)
  else
    match a with
    | ~q($x * $y) => 
      if x.hasMVar 
      then invertUSize x q($b / $y)
      else invertUSize y q($b / $x)
    | ~q($x / $y) => 
      if x.hasMVar 
      then invertUSize x q($b * $y)
      else invertUSize y q($x / $b)
    | ~q($x + $y) => 
      if x.hasMVar 
      then invertUSize x q($b - $y)
      else invertUSize y q($b - $x)
    | ~q($x - $y) => 
      if x.hasMVar 
      then invertUSize x q($b + $y)
      else invertUSize y q($x - $b)
    | _ => 
      throwError s!"`decuce_by` does not support USize operation {← ppExpr a}"


open Lean Meta Elab Tactic Qq
@[tactic deduceBy]  
partial def deduceByTactic : Tactic
| `(tactic| deduce_by $t:conv) => do

  let goal ← getMainGoal
  let .some (_,lhs,rhs) := Expr.eq? (← goal.getType) | throwError "expected `?m = e`, got {← ppExpr (← goal.getType)}"

  -- if ¬lhs.isMVar then
  --   throwError "lhs is not mvar"

  -- now we assume that a is mvar and b is and expression we want to simplify
  let (goal,a,b) ←
    if lhs.hasMVar then
      pure (goal,lhs,rhs)
    else 
      let goal' ← mkFreshExprMVar (← mkEq rhs lhs)
      goal.assign (← mkEqSymm goal')
      pure (goal'.mvarId!,rhs,lhs)

  let A ← inferType a
  if A == q(Nat) || A == q(USize) then
    let (m,x) ← 
      if A == q(Nat)
      then invertNat a b
      else invertUSize a b
    let (x', _) ← elabConvRewrite x t
    m.mvarId!.assign x'
    let subgoals ← evalTacticAt (← `(tactic| (conv => (conv => lhs; $t); (conv => rhs; $t)))) goal
    if subgoals.length ≠ 0 then
      throwError "`decide_by` failed to show {← ppExpr (← goal.getType)}"

  else
    let (b',prf) ← elabConvRewrite b t
    a.mvarId!.assign b'
    goal.assign prf
| _ => throwUnsupportedSyntax





