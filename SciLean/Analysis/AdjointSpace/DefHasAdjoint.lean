import SciLean.Analysis.AdjointSpace.HasAdjoint
-- import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.LSimp

namespace Scilean.Tactic.DataSynth.HasAdjoint

open SciLean

open Lean Elab Command Meta Qq

def getScalar? : MetaM (Option (Expr×Expr)) := do
  (← getLCtx).findDeclRevM? fun decl => do
    let type ← whnf decl.type
    dbg_trace (← ppExpr type)
    if (type.isAppOfArity ``RealScalar 1) ||
       (type.isAppOfArity ``RCLike 1) ||
       (type.isAppOfArity ``Scalar 2)  then
      return (decl.toExpr, decl.type.appArg!)
    else
      return none

def fixTypeUniverseQ (X : Expr) : MetaM ((u : Level) × Q(Type $u)) := do
  let .sort (Level.succ u) ← whnf (← inferType X) | throwError "not a type{indentExpr X}, has type {← ppExpr (← inferType X )}"
  return ⟨u,X⟩

def getScalarQ? : MetaM (Option ((u : Level) × (R : Q(Type u)) × Q(RCLike $R))) := do
  (← getLCtx).findDeclRevM? fun decl => do
    let type ← whnf decl.type
    if (type.isAppOfArity ``RealScalar 1) ||
       (type.isAppOfArity ``RCLike 1) ||
       (type.isAppOfArity ``Scalar 2) then
      let R := type.appArg!
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

    let goal ← mkAppM ``HasAdjoint #[R,f]
    -- eta expand rest of the arguments
    let goal ← forallTelescope (← inferType goal) fun ys _ =>
      mkForallFVars ys (goal.beta ys)

    let args := otherArgs++extraArgs
    let statement ← mkForallFVars args goal

    let fvars := (Lean.collectFVars {} statement).fvarIds
    if h : fvars.size ≠ 0 then
      throwError m!"resulting statement contains free variable {Expr.fvar fvars[0]}\n{statement}"

    let mvars := statement.collectMVars {} |>.result
    if h : mvars.size ≠ 0 then
      throwError m!"resulting statement contains meta variable {Expr.mvar mvars[0]}\n{statement}"

    return (statement,args.size,lvlNames)


open Qq in
elab "def_has_adjoint" fId:ident "in" args:ident* bs:bracketedBinder* "by" tac:tacticSeq : command => do

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
    let thmName := fId.append suffix |>.append `HasAdjoint_simple_rule

    -- let statement' := ← instantiateMVars (← mkForallFVars xs statement)

    -- -- let fvars := (Lean.collectFVars {} statement').fvarIds
    -- -- if h : fvars.size ≠ 0 then
    -- --   throwError m!"resulting statement contains free variable {Expr.fvar fvars[0]}\n{statement}"

    -- -- let mvars := statement'.collectMVars {} |>.result
    -- -- if h : mvars.size ≠ 0 then
    -- --   throwError m!"resulting statement contains meta variable {Expr.mvar mvars[0]}\n{statement}"

    -- let proof' := ← instantiateMVars (← mkLambdaFVars xs proof)

    -- IO.println s!"{← ppExpr statement'}"
    -- IO.println s!"{← ppExpr (← inferType proof')}"

    -- let fvars := (Lean.collectFVars {} proof').fvarIds
    -- if h : fvars.size ≠ 0 then
    --   throwError m!"resulting statement contains free variable {Expr.fvar fvars[0]}\n{statement}"

    -- let mvars := proof'.collectMVars {} |>.result
    -- if h : mvars.size ≠ 0 then
    --   throwError m!"resulting statement contains meta variable {Expr.mvar mvars[0]}\n{statement}"

    -- if statement'.hasMVar then
    --   throwError m!"proof has mvar"

    -- if proof'.hasMVar then
    --   throwError m!"statement has mvar"

    let thmVal : TheoremVal :=
    {
      name  := thmName
      type  := ← instantiateMVars (← mkForallFVars xs statement)
      value := ← instantiateMVars (← mkLambdaFVars xs proof)
      levelParams := lvls
    }

    addDecl (.thmDecl thmVal)
    Tactic.DataSynth.addTheorem thmName


variable {R} [RealScalar R] {X} [NormedAddCommGroup X] [AdjointSpace R X]

def foo (x y : X) :=
  let z := (3:R)•x + x
  x + (2:R)•(y + (4:R)•z)

def_has_adjoint foo in x y by
  unfold foo
  data_synth => dsimp -zeta
