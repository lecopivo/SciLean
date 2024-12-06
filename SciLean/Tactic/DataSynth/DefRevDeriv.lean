import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.Elab

namespace Scilean

open SciLean

open Lean Elab Command Meta

elab "def_rev_deriv" f:ident "in" args:ident* bs:bracketedBinder* "by" tac:tacticSeq : command => do

  Elab.Command.liftTermElabM <| do
  -- resolve function name
  let fId ← ensureNonAmbiguous f (← resolveGlobalConst f)
  let info ← getConstInfo fId

  forallTelescope info.type fun xs _ => do
  Elab.Term.elabBinders bs.raw fun ctx => do


    let args := args.map (fun id => id.getId)
    let (mainArgs, otherArgs) ← xs.splitM (fun x => do
      let n ← x.fvarId!.getUserName
      return args.contains n)

    -- check if all arguments are present
    for arg in args do
      if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != arg)) then
        throwError s!"function `{fId}` does not have argument `{arg}`"

    -- uncurry function appropriatelly
    let lvls := info.levelParams.map (fun p => Level.param p)
    let g ← liftM <|
      mkLambdaFVars mainArgs (mkAppN (Expr.const info.name lvls) xs)
      >>=
      mkUncurryFun mainArgs.size

    let some R ← xs.findSomeM? (fun x => do
      let X ← inferType x
      if X.isAppOf' ``SciLean.RealScalar then
        return X.appArg!
      else
        return none)
      | throwError "can't determine scalar"


    let goal ← mkAppM ``HasRevFDerivUpdate #[R,g]
    let (xs, _, goal') ← forallMetaTelescope (← inferType goal)
    let goal := goal.beta xs

    IO.println s!"initial: {← ppExpr goal}"

    let m ← mkFreshExprMVar goal

    let (_,_) ← runTactic m.mvarId! tac.raw

    IO.println s!"result: {← ppExpr (← instantiateMVars goal)}"

    let some goal ← Tactic.DataSynth.isDataSynthGoal? goal
      | throwError "invalid goal"

    pure ()


#check DataArrayN.outerprod

variable {R : Type} [RealScalar R] [PlainDataType R]
  (y : R^[n])

#check (HasRevFDerivUpdate R (fun x : R^[n]×R^[n] => x.1.outerprod x.2) _)
  rewrite_by
    data_synth

#check SciLean.DataArrayN.outerprod.arg_xy.HasRevFDerivUpdate


def Q (q : R^[D]) (l : R^[((D-1)*D)/2]) : R^[D,D] := q.exp.diag + l.lowerTriangular D 1

--set_option trace.Meta.Tactic.data_synth true in
-- set_option trace.Meta.isDefEq true in
def_rev_deriv Q in q l by --
  unfold Q
  data_synth =>
    enter[3]
    simp -zeta [DataArrayN.diag]





#check Simp.Config
