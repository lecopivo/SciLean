import Lean
import Qq
import Mathlib.Util.CompileInductive
import SciLean.Util.RewriteBy

open Lean Meta Qq Elab Tactic Conv

syntax (name:=conv_induction) "induction" ident (ident)? (ident)? (ident)? conv conv : conv

@[tactic conv_induction] def convInduction : Tactic
| `(conv| induction $n $[$n']? $[$prev]? $[$eq]? $baseConv $succConv) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lhs ← getLhs
    let .some decl := (← getLCtx).findFromUserName? n.getId
      | throwError s!"local variable {n} not found"

    let n := Expr.fvar decl.fvarId
    let lhsFun ← mkLambdaFVars #[n] lhs

    let (x₀, eq₀) ← convert (lhsFun.beta #[(.const ``Nat.zero [])]) (Tactic.evalTactic baseConv)

    let n' := n'.map   (fun x => x.getId) |>.getD (Name.appendAfter `n' "✝")
    let xₙ := prev.map (fun x => x.getId) |>.getD (Name.appendAfter `xₙ "✝")
    let eq := eq.map   (fun x => x.getId) |>.getD (Name.appendAfter `eq "✝")

    let (lhs',prf) ←
      withLocalDeclD n' (.const ``Nat []) fun n' => do
      withLocalDeclD xₙ (← inferType lhs) fun xₙ' => do
      withLocalDeclD eq (← mkEq (lhsFun.beta #[n']) xₙ') fun eqₙ' => do

        let (xSucc, eqSucc) ← convert (lhsFun.beta #[(← mkAppM ``Nat.succ #[n'])]) (Tactic.evalTactic succConv)

        let motive := Expr.lam default q(Nat) (← inferType lhs) default
        let base := x₀
        let succ ← mkLambdaFVars #[n',xₙ'] xSucc
        let recDef ← mkLambdaFVars #[n'] (← mkAppOptM ``Nat.recOn #[motive, n', base, succ])

        let motive ← mkLambdaFVars #[n'] ((← inferType eqₙ').replaceFVar xₙ' (recDef.beta #[n']))
        withLocalDeclD `eq (motive.beta #[n']) fun eqₙ'' => do
        let base := eq₀
        let succ ← mkLambdaFVars #[n',eqₙ''] (eqSucc.replaceFVars #[xₙ',eqₙ'] #[recDef.beta #[n'], eqₙ''])
        let recProof ← mkAppOptM ``Nat.recOn #[motive,n,base,succ]

        return (recDef.beta #[n],recProof)

    updateLhs lhs' prf

| _ => throwUnsupportedSyntax


syntax (name:=conv_induction_list) "induction_list" ident (ident)? (ident)? (ident)? (ident)? conv conv : conv

@[tactic conv_induction_list] def convInductionList : Tactic
| `(conv| induction_list $n $[$head]? $[$tail]? $[$prev]? $[$eq]? $baseConv $succConv) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lhs ← getLhs
    let .some decl := (← getLCtx).findFromUserName? n.getId
      | throwError s!"local variable {n} not found"

    let list := Expr.fvar decl.fvarId
    let lhsFun ← mkLambdaFVars #[list] lhs
    let .some type := (← instantiateMVars (← inferType list)).app1? ``List
      | throwError "{← ppExpr list} is not a list"

    let (x₀, eq₀) ← convert (lhsFun.beta #[← mkAppOptM ``List.nil #[type]]) (Tactic.evalTactic baseConv)

    let head := head.map (fun x => x.getId) |>.getD (Name.appendAfter `head "✝")
    let tail := tail.map (fun x => x.getId) |>.getD (Name.appendAfter `tail "✝")
    let prev := prev.map (fun x => x.getId) |>.getD (Name.appendAfter `prev "✝")
    let eq := eq.map     (fun x => x.getId) |>.getD (Name.appendAfter `eq "✝")

    let (lhs',prf) ←
      withLocalDeclD head type fun head => do
      withLocalDeclD tail (← inferType list) fun tail => do
      withLocalDeclD prev (← inferType lhs) fun prev => do
      let eqLhs := lhsFun.beta #[tail]
      withLocalDeclD eq (← mkEq eqLhs prev) fun eq => do

        let (xSucc, eqSucc) ← convert (lhsFun.beta #[(← mkAppM ``List.cons #[head,tail])]) (Tactic.evalTactic succConv)

        let motive := Expr.lam default (← inferType list) (← inferType lhs) default
        let base := x₀
        let succ ← mkLambdaFVars #[head,tail,prev] xSucc
        let recDef ← mkLambdaFVars #[list] (← mkAppOptM ``List.recOn #[none,motive, list, base, succ])

        let motive ← mkLambdaFVars #[list] ((← inferType eq).replaceFVars #[prev,tail] #[recDef.beta #[list], list])
        withLocalDeclD `eq (motive.beta #[tail]) fun eq' => do
        let base := eq₀
        let succ ← mkLambdaFVars #[head,tail,eq'] (eqSucc.replaceFVars #[prev,eq] #[recDef.beta #[tail], eq'])
        let recProof ← mkAppOptM ``List.recOn #[type,motive,list,base,succ]

        return (recDef.beta #[list],recProof)

    updateLhs lhs' prf

| _ => throwUnsupportedSyntax

-- theorem thm1 {n} : n.succ + n.succ = n + n + 2 := sorry

-- example (n : Nat) : n + n = (Nat.recOn n 0 fun n' xₙ => xₙ + 2) := by
--   conv =>
--     lhs
--     induction n n' xₙ eq
--       . simp
--       . rw[thm1,eq]
-- #check List.map (α:=Nat) (β:=Nat) id rewrite_by
--   enter [l]
--   induction_list l head tail prev eq
--     . simp[List.map]
--     . simp[List.map,eq]

-- def _root_.List.reduce (f : α → β → β)  (l : List α) (init : β) : β :=
--   match l with
--   | [] => init
--   | x :: xs =>  f x (reduce f xs init)

-- #check (fun l => 2 * List.reduce (init:=0) (·+·) l) rewrite_by
--   enter [l]
--   induction_list l head tail prev eq
--     . simp[List.reduce]
--     . simp[List.reduce]; rw[Nat.mul_add,eq]
