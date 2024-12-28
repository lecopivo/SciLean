import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
-- import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.Elab

namespace Scilean.Tactic.DataSynth

open SciLean

open Lean Elab Command Meta Qq

def getScalar? : MetaM (Option (Expr×Expr)) := do
  (← getLCtx).findDeclRevM? fun decl =>
    let type := decl.type
    if (type.isAppOfArity ``RealScalar 1) ||
       (type.isAppOfArity ``RCLike 1) then
      return (decl.toExpr, decl.type.appArg!)
    else
      return none

def fixTypeUniverseQ (X : Expr) : MetaM ((u : Level) × Q(Type $u)) := do
  let .sort (Level.succ u) ← inferType X | throwError "not a type{indentExpr X}"
  return ⟨u,X⟩

def getScalarQ? : MetaM (Option ((u : Level) × (R : Q(Type u)) × Q(RCLike $R))) := do
  (← getLCtx).findDeclRevM? fun decl => do
    let type := decl.type
    if (type.isAppOfArity ``RealScalar 1) ||
       (type.isAppOfArity ``RCLike 1) then
      let R := decl.type.appArg!
      let ⟨u,R⟩ ← fixTypeUniverseQ R
      let inst ← synthInstanceQ q(RCLike $R)
      return some ⟨u,R,inst⟩
    else
      return none


/-- For function `f` return `HasRevFDerivUpdate` statement in specified arguments `args`.

The result `(e,n,lvls)` is an expression `e` of the statement where the first `n` arguments are
considered as inputs and rest as output. `lvls` is list of universe parameter names.
-/
def getSimpleGoal (fId : Name) (argNames : Array Name)
    (extra : TSyntaxArray `Lean.Parser.Term.bracketedBinder) :
    TermElabM (Expr × ℕ × List Name) := do

  let info ← getConstInfo fId

  forallTelescope info.type fun xs _ => do
  Term.elabBinders extra.raw fun extraArgs => do

    -- split arguments `xs` into main and other
    let (mainArgs, otherArgs) ← xs.splitM (fun x => do
      let n ← x.fvarId!.getUserName
      return argNames.contains n)

    -- check if all arguments are present
    for argName in argNames do
      if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != argName)) then
        throwError s!"function `{fId}` does not have argument `{argName}`"

    -- find scalar field and its instance
    let some ⟨_,R,_⟩ ← getScalarQ?
      | throwError "can't determinal scalar field"

    let lvlNames := info.levelParams
    let lvls := lvlNames.map (fun p => Level.param p)
    let f ← liftM <|
      mkLambdaFVars mainArgs (mkAppN (Expr.const info.name lvls) xs)
      >>=
      mkUncurryFun' mainArgs.size

    let goal ← mkAppM ``HasRevFDerivUpdate #[R,f]
    -- eta expand rest of the arguments
    let goal ← forallTelescope (← inferType goal) fun ys _ =>
      mkForallFVars ys (goal.beta ys)

    let args := otherArgs++extraArgs
    let statement ← mkForallFVars args goal
    return (statement,args.size,lvlNames)


def getCompositionalGoal (fId : Name) (argNames : Array Name)
    (extra : TSyntaxArray `Lean.Parser.Term.bracketedBinder) :
    TermElabM (Expr × ℕ × List Name) := do

  let info ← getConstInfo fId

  forallTelescope info.type fun xs _ => do
  Term.elabBinders extra.raw fun _extraArgs => do

    -- split arguments `xs` into main and other
    let (mainArgs, otherArgs) ← xs.splitM (fun x => do
      let n ← x.fvarId!.getUserName
      return argNames.contains n)

    -- check if all arguments are present
    for argName in argNames do
      if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != argName)) then
        throwError s!"function `{fId}` does not have argument `{argName}`"

    -- find scalar field and its instance
    let some ⟨_,R,_⟩ ← getScalarQ?
      | throwError "can't determinal scalar field"

    -- introduce
    withLocalDeclQ `W .implicit q(Type) fun W => do
    withLocalDeclQ `inst1 .instImplicit q(NormedAddCommGroup $W) fun inst1 => do
    withLocalDeclQ `inst2 .instImplicit q(AdjointSpace $R $W) fun inst2 => do
    withLocalDeclQ `inst3 .instImplicit q(CompleteSpace $W) fun inst3 => do

    -- prepare names and types for main arguments parametrized by `W`
    let xnames ← mainArgs.mapM (fun x => x.fvarId!.getUserName)
    let xnames' := xnames.map (fun n => n.appendAfter "'")
    let hxnames := xnames.map (fun n => n.appendBefore "h")
    let xtypes ← mainArgs.mapM (fun x => do mkArrow W (← inferType x))
    let xtypes' ← mainArgs.mapM (fun x => do
      let W := (← checkTypeQ W q(Type)).get!
      let X := (← checkTypeQ (← inferType x) q(Type)).get!
      return q($W → $X×($X → $W → $W)))

    withLocalDecls' xnames default xtypes fun args => do
    withLocalDecls' xnames' default xtypes' fun args' => do
    let hxtypes ← (args.zip args').mapM (fun (arg,arg') => mkAppM ``HasRevFDerivUpdate #[R,arg,arg'])
    withLocalDecls' hxnames default hxtypes fun hargs => do


    let lvlNames := info.levelParams
    let _lvls := lvlNames.map (fun p => Level.param p)
    let f ←
      withLocalDecl `w default W fun w => do
        let vals := args.map (fun x => x.app w)
        mkLambdaFVars #[w] ((← mkAppOptM fId (xs.map some)).replaceFVars mainArgs vals)

    let args := otherArgs ++ (#[W,inst1,inst2,inst3] : Array Expr) ++ args ++ args' ++ hargs
    let statement ← mkAppM ``HasRevFDerivUpdate #[R,f]
    -- eta expand rest of the arguments
    let statement ← forallTelescope (← inferType statement) fun ys _ =>
      mkForallFVars ys (statement.beta ys)
    let statement ← mkForallFVars args statement

    return (statement, args.size, lvlNames)


open Qq in
elab "def_rev_deriv" fId:ident "in" args:ident* bs:bracketedBinder* "by" tac:tacticSeq : command => do

  Elab.Command.liftTermElabM <| do
  -- resolve function name
  let fId ← ensureNonAmbiguous fId (← resolveGlobalConst fId)
  let argNames := args.map (fun id => id.getId)

  let (simpleGoal,n,lvls) ← getSimpleGoal fId argNames bs
  -- let (compGoal,m,lvls') ← getCompositionalGoal fId argNames bs

  forallBoundedTelescope simpleGoal n fun xs e => do
    let (_,_,statement) ← forallMetaTelescope (← etaExpand e)

    let proof ← mkFreshExprMVar statement
    let (_,_) ← runTactic proof.mvarId! tac

    let suffix := (argNames.foldl (init:=`arg_) (·.appendAfter ·.toString))
    let thmName := fId.append suffix |>.append `HasRevFDeriv_simple_rule

    let thmVal : TheoremVal :=
    {
      name  := thmName
      type  := ← instantiateMVars (← mkForallFVars xs statement)
      value := ← instantiateMVars (← mkLambdaFVars xs proof)
      levelParams := lvls
    }

    addDecl (.thmDecl thmVal)
    Tactic.DataSynth.addTheorem thmName


open Qq in
elab "def_rev_deriv'" fId:ident "in" args:ident* bs:bracketedBinder* "by" tac:tacticSeq : command => do

  Elab.Command.liftTermElabM <| do
  -- resolve function name
  let fId ← ensureNonAmbiguous fId (← resolveGlobalConst fId)
  let argNames := args.map (fun id => id.getId)

  let (compGoal,n,lvls) ← getCompositionalGoal fId argNames bs

  forallBoundedTelescope compGoal n fun xs e => do
    let (_,_,statement) ← forallMetaTelescope (← etaExpand e)

    let proof ← mkFreshExprMVar statement
    let (_,_) ← runTactic proof.mvarId! tac

    let suffix := (argNames.foldl (init:=`arg_) (·.appendAfter ·.toString))
    let thmName := fId.append suffix |>.append `HasRevFDeriv_comp_rule

    let thmVal : TheoremVal :=
    {
      name  := thmName
      type  := ← instantiateMVars (← mkForallFVars xs statement)
      value := ← instantiateMVars (← mkLambdaFVars xs proof)
      levelParams := lvls
    }

    addDecl (.thmDecl thmVal)
    Tactic.DataSynth.addTheorem thmName
