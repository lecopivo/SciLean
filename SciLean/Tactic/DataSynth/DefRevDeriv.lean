-- import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
-- import SciLean.Tactic.DataSynth.ArrayOperations
import SciLean.Tactic.DataSynth.Elab

namespace SciLean.Tactic.DataSynth

open SciLean
open Lean Elab Command Meta Qq

-- TODO: salvage `getCompositionalGoal` and remove this file

-- def getScalar? : MetaM (Option (Expr×Expr)) := do
--   (← getLCtx).findDeclRevM? fun decl => do
--     let type ← whnf decl.type
--     dbg_trace (← ppExpr type)
--     if (type.isAppOfArity ``RealScalar 1) ||
--        (type.isAppOfArity ``RCLike 1) ||
--        (type.isAppOfArity ``Scalar 2)  then
--       return (decl.toExpr, decl.type.appArg!)
--     else
--       return none

-- def fixTypeUniverseQ (X : Expr) : MetaM ((u : Level) × Q(Type $u)) := do
--   let .sort (Level.succ u) ← whnf (← inferType X) | throwError "not a type{indentExpr X}, has type {← ppExpr (← inferType X )}"
--   return ⟨u,X⟩

-- def getScalarQ? : MetaM (Option ((u : Level) × (R : Q(Type u)) × Q(RCLike $R))) := do
--   (← getLCtx).findDeclRevM? fun decl => do
--     let type ← whnf decl.type
--     if (type.isAppOfArity ``RealScalar 1) ||
--        (type.isAppOfArity ``RCLike 1) ||
--        (type.isAppOfArity ``Scalar 2) then
--       let R := type.appArg!
--       let ⟨u,R⟩ ← fixTypeUniverseQ R
--       let inst ← synthInstanceQ q(RCLike $R)
--       return some ⟨u,R,inst⟩
--     else
--       return none


-- /-- For function `f` return `HasRevFDerivUpdate` statement in specified arguments `args`.

-- The result `(e,n,lvls)` is an expression `e` of the statement where the first `n` arguments are
-- considered as inputs and rest as output. `lvls` is list of universe parameter names.
-- -/
-- def getSimpleGoal (fId : Name) (argNames : Array Name)
--     (extra : TSyntaxArray `Lean.Parser.Term.bracketedBinder) :
--     TermElabM (Expr × ℕ × List Name) := do

--   let info ← getConstInfo fId

--   forallTelescope info.type fun xs _ => do
--   Term.elabBinders extra.raw fun extraArgs => do

--     -- split arguments `xs` into main and other
--     let (mainArgs, otherArgs) ← xs.splitM (fun x => do
--       let n ← x.fvarId!.getUserName
--       return argNames.contains n)

--     -- check if all arguments are present
--     for argName in argNames do
--       if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != argName)) then
--         throwError s!"function `{fId}` does not have argument `{argName}`"

--     -- find scalar field and its instance
--     let some ⟨_,R,_⟩ ← getScalarQ?
--       | throwError "can't determinal scalar field"

--     let lvlNames := info.levelParams
--     let lvls := lvlNames.map (fun p => Level.param p)
--     let f ← liftM <|
--       mkLambdaFVars mainArgs (mkAppN (Expr.const info.name lvls) xs)
--       >>=
--       mkUncurryFun' mainArgs.size

--     let goal ← mkAppM ``HasRevFDerivUpdate #[R,f]
--     -- eta expand rest of the arguments
--     let goal ← forallTelescope (← inferType goal) fun ys _ =>
--       mkForallFVars ys (goal.beta ys)

--     let args := otherArgs++extraArgs
--     let statement ← mkForallFVars args goal
--     return (statement,args.size,lvlNames)

-- private partial def mkUnusedName (names : List Name) (baseName : Name) : Name :=
--   if not (names.contains baseName) then
--     baseName
--   else
--     let rec loop (i : Nat := 0) : Name :=
--       let w := Name.appendIndexAfter baseName i
--       if names.contains w then
--         loop (i + 1)
--       else
--         w
--     loop 1


-- def getCompositionalGoal (fId : Name) (argNames : Array Name)
--     (extra : TSyntaxArray `Lean.Parser.Term.bracketedBinder) :
--     TermElabM (Expr × ℕ × List Name) := do

--   let info ← getConstInfo fId

--   forallTelescope info.type fun xs _ => do
--   Term.elabBinders extra.raw fun extraArgs => do

--     -- split arguments `xs` into main and other
--     let (mainArgs, otherArgs) ← xs.splitM (fun x => do
--       let n ← x.fvarId!.getUserName
--       return argNames.contains n)

--     -- check if all arguments are present
--     for argName in argNames do
--       if ← mainArgs.allM (fun a => do pure ((← a.fvarId!.getUserName) != argName)) then
--         throwError s!"function `{fId}` does not have argument `{argName}`"

--     -- find scalar field and its instance
--     let some ⟨_,R,_⟩ ← getScalarQ?
--       | throwError "can't determinal scalar field"

--     -- gather universe params
--     let lvlNames := info.levelParams
--     let u := mkUnusedName lvlNames `u
--     let lvlNames := u :: lvlNames
--     let u : Level := Level.param u

--     -- introduce auxiliary space
--     withLocalDecl `W .implicit q(Type $u) fun W => do -- todo: make universe polymorphic
--     withLocalDecl `inst1 .instImplicit (← mkAppM ``NormedAddCommGroup #[W]) fun inst1 => do
--     withLocalDecl `inst2 .instImplicit (← mkAppOptM ``AdjointSpace #[R,W,none,none]) fun inst2 => do
--     withLocalDecl `inst3 .instImplicit (← mkAppOptM ``CompleteSpace #[W,none]) fun inst3 => do

--     -- prepare names and types for main arguments parametrized by `W`
--     let xnames ← mainArgs.mapM (fun x => x.fvarId!.getUserName)
--     let xnames' := xnames.map (fun n => n.appendAfter "'")
--     let hxnames := xnames.map (fun n => n.appendBefore "h")
--     let xtypes ← mainArgs.mapM (fun x => do mkArrow W (← inferType x))
--     let xtypes' ← mainArgs.mapM (fun x => do
--       let X ← inferType x
--       -- construct expr for `W → X×(X→W→W)`
--       let XWW ← mkArrow X (← mkArrow W W)
--       let XXWW ← mkAppM ``Prod #[X,XWW]
--       let WXXWW ← mkArrow W XXWW
--       pure WXXWW)

--     withLocalDecls' xnames default xtypes fun args => do
--     withLocalDecls' xnames' default xtypes' fun args' => do
--     let hxtypes ← (args.zip args').mapM (fun (arg,arg') => mkAppM ``HasRevFDerivUpdate #[R,arg,arg'])
--     withLocalDecls' hxnames default hxtypes fun hargs => do

--     let f ←
--       withLocalDecl `w default W fun w => do
--         let vals := args.map (fun x => x.app w)
--         mkLambdaFVars #[w] ((← mkAppOptM fId (xs.map some)).replaceFVars mainArgs vals)

--     let args := otherArgs ++ extraArgs ++ (#[W,inst1,inst2,inst3] : Array Expr) ++ args ++ args' ++ hargs
--     let statement ← mkAppM ``HasRevFDerivUpdate #[R,f]
--     -- eta expand rest of the arguments
--     let statement ← forallTelescope (← inferType statement) fun ys _ =>
--       mkForallFVars ys (statement.beta ys)
--     let statement ← mkForallFVars args statement

--     let fvars := (Lean.collectFVars {} statement).fvarIds
--     if h : fvars.size ≠ 0 then
--       throwError m!"resulting statement contains free variable {Expr.fvar fvars[0]}\n{statement}"

--     let fvars := (Lean.collectFVars {} statement).fvarIds
--     if h : fvars.size ≠ 0 then
--       throwError m!"resulting statement contains free variable {Expr.fvar fvars[0]}\n{statement}"

--     let mvars := statement.collectMVars {} |>.result
--     if h : mvars.size ≠ 0 then
--       throwError m!"resulting statement contains meta variable {Expr.mvar mvars[0]}\n{statement}"

--     return (statement, args.size, lvlNames)


-- open Qq in
-- elab "def_rev_deriv" fId:ident "in" args:ident* bs:bracketedBinder* "by" tac:tacticSeq : command => do

--   Elab.Command.liftTermElabM <| do
--   -- resolve function name
--   let fId ← ensureNonAmbiguous fId (← resolveGlobalConst fId)
--   let argNames := args.map (fun id => id.getId)

--   let (simpleGoal,n,lvls) ← getSimpleGoal fId argNames bs
--   -- let (compGoal,m,lvls') ← getCompositionalGoal fId argNames bs

--   forallBoundedTelescope simpleGoal n fun xs e => do
--     let (_,_,statement) ← forallMetaTelescope (← etaExpand e)

--     let proof ← mkFreshExprMVar statement
--     let (_,_) ← runTactic proof.mvarId! tac

--     let suffix := (argNames.foldl (init:=`arg_) (·.appendAfter ·.toString))
--     let thmName := fId.append suffix |>.append `HasRevFDerivUpdate_simple_rule

--     let thmVal : TheoremVal :=
--     {
--       name  := thmName
--       type  := ← instantiateMVars (← mkForallFVars xs statement)
--       value := ← instantiateMVars (← mkLambdaFVars xs proof)
--       levelParams := lvls
--     }

--     addDecl (.thmDecl thmVal)
--     Tactic.DataSynth.addTheorem thmName


-- open Qq in
-- elab "def_rev_deriv'" fId:ident "in" args:ident* bs:bracketedBinder* "by" tac:tacticSeq : command => do

--   Elab.Command.liftTermElabM <| do
--   -- resolve function name
--   let fId ← ensureNonAmbiguous fId (← resolveGlobalConst fId)
--   let argNames := args.map (fun id => id.getId)

--   let (compGoal,n,lvls) ← getCompositionalGoal fId argNames bs

--   forallBoundedTelescope compGoal n fun xs e => do
--     let (_,_,statement) ← forallMetaTelescope (← etaExpand e)

--     let proof ← mkFreshExprMVar statement
--     let (_,_) ← runTactic proof.mvarId! tac

--     let suffix := (argNames.foldl (init:=`arg_) (·.appendAfter ·.toString))
--     let thmName := fId.append suffix |>.append `HasRevFDerivUpdate_comp_rule

--     let thmVal : TheoremVal :=
--     {
--       name  := thmName
--       type  := ← instantiateMVars (← mkForallFVars xs statement)
--       value := ← instantiateMVars (← mkLambdaFVars xs proof)
--       levelParams := lvls
--     }

--     addDecl (.thmDecl thmVal)
--     Tactic.DataSynth.addTheorem thmName



-- def foo {R} [RealScalar R] (x : R) := x + x

-- def_rev_deriv foo in x by
--   unfold foo
--   data_synth =>
--     enter [3]
--     ring_nf
