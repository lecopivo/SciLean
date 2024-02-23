import Lean
import Qq
import Mathlib.Util.CompileInductive

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

-- theorem thm1 {n} : n.succ + n.succ = n + n + 2 := sorry

-- example (n : Nat) : n + n = (Nat.recOn n 0 fun n' xₙ => xₙ + 2) := by
--   conv =>
--     lhs
--     induction n n' xₙ eq
--       . simp
--       . rw[thm1,eq]
