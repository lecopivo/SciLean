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

#check List.recOn
@[tactic conv_induction_list] def convInductionList : Tactic
| `(conv| induction_list $n $[$head]? $[$tail]? $[$prev]? $[$eq]? $baseConv $succConv) => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let lhs ← getLhs
    let .some decl := (← getLCtx).findFromUserName? n.getId
      | throwError s!"local variable {n} not found"

    let list := Expr.fvar decl.fvarId
    let lhsFun ← mkLambdaFVars #[list] lhs
    IO.println (← ppExpr (← inferType list))
    IO.println ((← instantiateMVars (← inferType list)).isAppOf ``List)
    let .some type := (← instantiateMVars (← inferType list)).app1? ``List
      | throwError "{← ppExpr list} is not a list"

    let (x₀, eq₀) ← convert (lhsFun.beta #[← mkAppOptM ``List.nil #[type]]) (Tactic.evalTactic baseConv)

    let head := head.map (fun x => x.getId) |>.getD (Name.appendAfter `head "✝")
    let tail := tail.map (fun x => x.getId) |>.getD (Name.appendAfter `tail "✝")
    let prev := prev.map (fun x => x.getId) |>.getD (Name.appendAfter `prev "✝")
    let eq := eq.map     (fun x => x.getId) |>.getD (Name.appendAfter `eq "✝")

    IO.println "hihi"

    let (lhs',prf) ←
      withLocalDeclD head type fun head => do
      withLocalDeclD tail (← inferType lhs) fun tail => do
      withLocalDeclD prev (← inferType lhs) fun prev => do
      let eqLhs := lhsFun.beta #[tail]
      withLocalDeclD eq (← mkEq eqLhs prev) fun eq => do

        let (xSucc, eqSucc) ← convert (lhsFun.beta #[(← mkAppM ``List.cons #[head,tail])]) (Tactic.evalTactic succConv)

        IO.println "hi 2"
        let motive := Expr.lam default (← inferType list) (← inferType lhs) default
        let base := x₀
        let succ ← mkLambdaFVars #[head,tail,prev] xSucc
        let recDef ← mkLambdaFVars #[list] (← mkAppOptM ``List.recOn #[none,motive, list, base, succ])
        IO.println s!"recDef: {← ppExpr recDef}"
        return (0,1)

        -- let motive ← mkLambdaFVars #[head] ((← inferType eq).replaceFVar head (recDef.beta #[tail]))
        -- withLocalDeclD `eq (motive.beta #[head]) fun eq' => do
        -- let base := eq₀
        -- let succ ← mkLambdaFVars #[tail,eq'] (eqSucc.replaceFVars #[tail,eq] #[recDef.beta #[head], eq'])
        -- let recProof ← mkAppOptM ``List.recOn #[motive,list,base,succ]
        -- IO.println "hi 4"
        -- return (recDef.beta #[list],recProof)

    -- updateLhs lhs' prf

| _ => throwUnsupportedSyntax

-- theorem thm1 {n} : n.succ + n.succ = n + n + 2 := sorry

-- example (n : Nat) : n + n = (Nat.recOn n 0 fun n' xₙ => xₙ + 2) := by
--   conv =>
--     lhs
--     induction n n' xₙ eq
--       . simp
--       . rw[thm1,eq]
#check List.map (α:=Nat) (β:=Nat) id rewrite_by
  enter [l]
  induction_list l head tail prev eq
    . simp[List.map]
    . simp[List.map,eq]
