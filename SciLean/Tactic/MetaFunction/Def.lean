import SciLean.Tactic.MetaFunction.Decl

open Lean Meta Elab Command

namespace SciLean.Tactic.MetaFun

open Syntax Parser Command
elab "meta_fun_def" prio:optNamedPrio thmName:ident bs:bracketedBinder* ":" lhs:term ":=" rhs:term "satisfied_by" tac:tacticSeq : command => do
  runTermElabM fun ctx => do
  Term.elabBinders bs fun xs => do
  let lhs ← Term.elabTermAndSynthesize lhs none
  let rhs ← Term.elabTermAndSynthesize rhs (← inferType lhs)


  let (fId,args) := lhs.getAppFnArgs
  let .some decl ← getDeclFromFun? fId
    | throwError m!"{lhs} is expected to be application of meta-function"
  let FId := decl.metaFunPropName

  let lhs' ← mkAppOptM FId (args.map Option.some)
  -- logInfo m!"lhs' {lhs'}"

  -- find applications of meta-functions and replace them with fresh fvars
  -- it is done bottom up as we might have nested applications of meta-functions
  let rhsM := Meta.transform (m:=StateT (Array Expr) MetaLCtxM)
    (input := rhs)
    (post := fun e => do

      let xs ← get

      let (fn,args) := e.getAppFnArgs
      let .some decl ← getDeclFromFun? fn
        | return .done e

      let arity ← getConstArity decl.metaFunName
      unless arity = args.size do return .done e

      let name := ((`a).appendAfter s!"{xs.size/2}")
      let a ← introLocalDecl name default (← inferType e)
      let prop ← mkAppOptM decl.metaFunPropName (args.map Option.some |>.push a)
      let hname := name.appendBefore "h"
      let ha ← introLocalDecl hname default prop

      set (xs ++ #[a,ha])

      -- logInfo m!"replacing {e} ==> {a}"

      return .done a)

  let statement ←
    (rhsM.run #[]).runInMeta (fun (rhs',xs) => do
      mkForallFVars xs (lhs'.app rhs'))

  let prf ← Term.elabTermAndSynthesize (← `(by ($tac))) statement
  -- logInfo m!"theorem statement {statement}"
  -- logInfo m!"theorem prf {prf}"

  let prf ← mkLambdaFVars xs prf
  let statement ← mkForallFVars xs statement

  -- filter context - this is error prone!
  -- somehow use: withHeaderSecVars
  let ctx' := ctx.filter (fun v => statement.containsFVar v.fvarId!)

  let prf ← mkLambdaFVars ctx' prf >>= instantiateMVars
  let statement ← mkForallFVars ctx' statement >>= instantiateMVars

  let lvls := (collectLevelParams {} statement).params

  let decl' : DefinitionVal := {
    name := thmName.getId
    levelParams := lvls.toList
    value := prf
    type := statement
    hints := .regular 0
    safety := .safe
  }

  let decl : TheoremVal := {
    name := thmName.getId
    levelParams := lvls.toList
    value := prf
    type := statement
  }

  try
    addDecl (.thmDecl decl)
  catch _ =>
    addAndCompile (.defnDecl decl')

  let prio ← liftMacroM <| expandOptNamedPrio prio

  SciLean.Tactic.DataSynth.addTheorem thmName.getId (kind:=.global) (prio:=prio)
