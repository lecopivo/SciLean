import SciLean.Analysis.Scalar
import SciLean.Tactic.DataSynth.Elab

namespace SciLean.Tactic.DataSynth

open SciLean

open Lean Elab Command Meta Qq


/-- For function `f` return `HasRevFDerivUpdate` statement in specified arguments `args`.

The result `(e,n,lvls)` is an expression `e` of the statement where the first `n` arguments are
considered as inputs and rest as output. `lvls` is list of universe parameter names.
-/
def getSimpleGoal' (dataSynthStatement : TSyntax `term) (fId : Name) (argNames : Array Name)
    (extra : TSyntaxArray `Lean.Parser.Term.bracketedBinder) :
    TermElabM (Expr × ℕ × List Name) := do

  let info ← getConstInfo fId

  forallTelescope info.type fun xs _ => do
  -- todo: this can introduce new level mvars, please handle them!!!
  Term.elabBinders extra.raw fun extraArgs => do

    -- split arguments `xs` into main and other
    let (mainArgs, otherArgs) ← xs.splitM (fun x => do
      let n ← x.fvarId!.getUserName
      return argNames.contains n)

    -- check if all arguments are present
    for argName in argNames do
      if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != argName)) then
        throwError s!"function `{fId}` does not have argument `{argName}`"

    let lvlNames := info.levelParams
    let lvls := lvlNames.map (fun p => Level.param p)
    let f ← liftM <|
      mkLambdaFVars mainArgs (mkAppN (Expr.const info.name lvls) xs)
      >>=
      mkUncurryFun' mainArgs.size

    let dataSynthType ← mkArrow (← inferType f) (← mkFreshTypeMVar)
    let dataSynthFun ← Elab.Term.elabTerm dataSynthStatement dataSynthType
    let goal := dataSynthFun.beta #[f]
    -- eta expand rest of the arguments
    let goal ← forallTelescope (← inferType goal) fun ys _ =>
      mkForallFVars ys (goal.beta ys)

    let args := otherArgs++extraArgs
    let statement ← mkForallFVars args goal

    return (statement,args.size,lvlNames)

open Qq in
def abbrevDataSynth (dataSynthStatement : TSyntax `term) (fId : Ident)
    (args : TSyntaxArray `ident)
    (bs : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) : CommandElabM Unit := do

  Elab.Command.liftTermElabM <| do
  -- resolve function name

  let fId ← ensureNonAmbiguous fId (← resolveGlobalConst fId)
  let argNames := args.map (fun id => id.getId)

  let (simpleGoal,n,lvls) ← getSimpleGoal' dataSynthStatement fId argNames bs

  forallBoundedTelescope simpleGoal n fun xs e => do
    let (_,_,statement) ← forallMetaTelescope (← etaExpand e)
    let .some dataSynthDecl ← isDataSynth? statement
      | throwError s!"not data_synth goal {← ppExpr statement}"

    let proof ← mkFreshExprMVar statement
    let (_,_) ← runTactic proof.mvarId! tac

    let suffix := (argNames.foldl (init:=`arg_) (·.appendAfter ·.toString))
    let thmName := fId.append suffix |>.append (dataSynthDecl.name.appendAfter "simple_rule")

    let thmVal : TheoremVal :=
    {
      name  := thmName
      type  := ← instantiateMVars (← mkForallFVars xs statement)
      value := ← instantiateMVars (← mkLambdaFVars xs proof)
      levelParams := lvls
    }

    addDecl (.thmDecl thmVal)
    Tactic.DataSynth.addTheorem thmName


elab "abbrev_data_synth" fId:ident
       "in"  args:ident* bs:bracketedBinder*
       " : " dataSynthStatement:term
       "by"  tac:tacticSeq : command => do
  Tactic.DataSynth.abbrevDataSynth dataSynthStatement fId args bs tac
