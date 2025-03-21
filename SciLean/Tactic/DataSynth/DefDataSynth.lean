import SciLean.Analysis.Scalar
import SciLean.Tactic.DataSynth.Elab

namespace SciLean.Tactic.DataSynth

open SciLean

open Lean Elab Command Meta Qq

-- todo: use local environment extension
initialize dataSynthVariableBinders : IO.Ref (TSyntaxArray `Lean.Parser.Term.bracketedBinder) ← ST.mkRef {}

elab "data_synth_variable " bs:bracketedBinder* : command => do
  dataSynthVariableBinders.set bs


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
  let variableBinders ← dataSynthVariableBinders.get
  Term.elabBinders (variableBinders ++ extra).raw fun extraArgs => do

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
      mkUncurryFun' mainArgs.size (withLet := false)

    let dataSynthType ← mkArrow (← inferType f) (← mkFreshTypeMVar)
    let dataSynthFun ← Elab.Term.elabTerm dataSynthStatement dataSynthType
    let goal := dataSynthFun.beta #[f]
    -- eta expand rest of the arguments
    let goal ← forallTelescope (← inferType goal) fun ys _ =>
      mkForallFVars ys (goal.beta ys)

    let args := otherArgs++extraArgs
    let statement ← mkForallFVars args goal

    let lvls := (collectLevelParams {} statement).params

    return (statement,args.size,lvls.toList/-lvlNames-/)


def checkNoMVars (e : Expr) : MetaM Unit := do
  let mvars := (e.collectMVars {}).result
  if h : 0 < mvars.size then
    throwError m!"{e} containt mvar {mvars[0]}"
  let valLvlMVars := (collectLevelMVars {} e).result
  if h : 0 < valLvlMVars.size then
    throwError m!"{e} containt level mvar {Level.mvar valLvlMVars[0]}"

def checkNoMVarsInForallBinders (e : Expr) : MetaM Unit := do

  forallTelescope e fun xs _ => do
    for x in xs do
      let tx ← inferType x
      if tx.hasMVar then
        throwError m!"({x} : {tx}) containt level mvar!"

open Qq in
def abbrevDataSynth (dataSynthStatement : TSyntax `term) (fId : Ident)
    (args : TSyntaxArray `ident)
    (bs : TSyntaxArray `Lean.Parser.Term.bracketedBinder)
    (tac : TSyntax `Lean.Parser.Tactic.tacticSeq)
    (useDef := false) : CommandElabM Unit := do

  Elab.Command.liftTermElabM <| do
  -- resolve function name

  let fId ← ensureNonAmbiguous fId (← resolveGlobalConst fId)
  let argNames := args.map (fun id => id.getId)

  let (simpleGoal,n,lvls) ← getSimpleGoal' dataSynthStatement fId argNames bs
  let simpleGoal ← instantiateMVars simpleGoal

  forallBoundedTelescope simpleGoal n fun xs e => do
    let mut (_,_,statement) ← forallMetaTelescope (← etaExpand e)
    let .some dataSynthDecl ← isDataSynth? statement
      | throwError s!"not data_synth goal {← ppExpr statement}"

    let proof ← mkFreshExprMVar statement
    let (_,_) ← runTactic proof.mvarId! tac

    let suffix := (argNames.foldl (init:=`arg_) (·.appendAfter ·.toString))
    let thmName := fId.append suffix
      |>.append (.mkSimple s!"{dataSynthDecl.name.getString!}_simple_rule")

    if useDef then
      let argNames ← getConstArgNames dataSynthDecl.name
      for outArgId in dataSynthDecl.outputArgs do
        let output ← instantiateMVars (statement.getArg! outArgId)
        let defName := fId.append suffix
          |>.append (.mkSimple s!"{dataSynthDecl.name.getString!}_{argNames[outArgId]!}")

        -- filter input arguments to the minimal required
        let xs' := xs.filter (fun x => output.containsFVar x.fvarId!)

        let val ← mkLambdaFVars xs' output
        let type ← inferType val

        checkNoMVars val
        checkNoMVars type

        -- gel all level args
        let lvls' := (collectLevelParams {} type).params

        let defVal : DefinitionVal := {
          name  := defName
          type  := type
          value := val
          hints := .regular 0
          safety := .safe
          levelParams := lvls'.toList
        }

        addDecl (.defnDecl defVal)
        try
          compileDecl (.defnDecl defVal)
        catch _ =>
          throwError "failed to complie {defName}!"
        let lvls' := lvls'.map (Level.param) |>.toList
        if useDef then
          statement := statement.setArg outArgId (mkAppN (.const defName lvls') xs')

    let ty :=  ← instantiateMVars (← mkForallFVars xs statement)
    let val := ← instantiateMVars (← mkLambdaFVars xs proof)

    checkNoMVars ty
    checkNoMVars val
    checkNoMVarsInForallBinders ty

    let thmVal : TheoremVal :=
    {
      name  := thmName
      type  := ty
      value := val
      levelParams := lvls
    }

    addDecl (.thmDecl thmVal)
    Tactic.DataSynth.addTheorem thmName


elab "abbrev_data_synth" fId:ident
       "in"  args:ident* bs:bracketedBinder*
       " : " dataSynthStatement:term
       "by"  tac:tacticSeq : command => do
  Tactic.DataSynth.abbrevDataSynth dataSynthStatement fId args bs tac (useDef:=false)

elab "def_data_synth" fId:ident
       "in"  args:ident* bs:bracketedBinder*
       " : " dataSynthStatement:term
       "by"  tac:tacticSeq : command => do
  Tactic.DataSynth.abbrevDataSynth dataSynthStatement fId args bs tac (useDef:=true)
