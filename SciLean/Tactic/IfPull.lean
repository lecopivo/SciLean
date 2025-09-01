import Lean
import SciLean.Util.RewriteBy
import SciLean.Util.SorryProof

namespace SciLean.Tactic

open Lean Meta

initialize registerTraceClass `Meta.Tactic.if_pull

/-- Simproc that pulls `if` out of applications and lambda functions.

For example
  - `(if 0 ≤ x then x else -x) + y` is transformed to `if 0 ≤ x then x + y else -x + y`
  - `fun y => if 0 ≤ x then y + x else y - x` is transformed to `if 0 ≤ x then (fun y => y + x) else (fun y => y - x)`  -/
simproc_decl if_pull (_) := fun e => do

  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs

    let mut thn : Expr := default
    let mut els : Expr := default
    let mut cond : Expr := default

    -- do not pull `if` out of `if`
    -- this would cause infinite loops
    if e.isAppOf ``ite then
      if args.size ≤ 5 then
        return .continue
      else
        thn := mkAppN (e.getArg! 3) args[5:]
        els := mkAppN (e.getArg! 4) args[5:]
        cond := e.getArg! 1
    else
      -- locate argument with if statement
      let .some i := args.findIdx? fun arg => arg.isAppOfArity ``ite 5
        | return .continue

      let arg := args[i]!
      -- todo: introduce let bindings for other arguments (probaly only for non-type arguments)
      thn := mkAppN fn (args.set! i (arg.getArg! 3))
      els := mkAppN fn (args.set! i (arg.getArg! 4))
      cond := arg.getArg! 1

    let e' ← mkAppOptM ``ite #[none, cond, none, thn, els]

    let prf := Expr.app (Expr.const ``SciLean.sorryProofAxiom []) (← mkEq e e')

    trace[Meta.Tactic.if_pull] s!"if_pull: \n{← ppExpr e}\n==>\n{← ppExpr e'}\n"
    return .visit { expr := e', proof? := prf }

  | .lam ..
  | .letE .. =>

    lambdaLetTelescope e fun xs b => do

    unless b.isAppOfArity ``ite 5 do return .continue
    let cond := b.getArg! 1
    let i := xs.reverse.findIdx? (fun x => cond.containsFVar x.fvarId!) |>.getD xs.size

    unless i > 0 do return .continue

    let xs' := xs[0:xs.size-i]
    let xs'' := xs[xs.size-i:]

    let thn ← mkLambdaFVars xs'' (b.getArg! 3)
    let els ← mkLambdaFVars xs'' (b.getArg! 4)

    let e' ← mkAppOptM ``ite #[none, b.getArg! 1, none, thn, els]
    let e' ← mkLambdaFVars xs' e'

    let prf := Expr.app (Expr.const ``SciLean.sorryProofAxiom []) (← mkEq e e')

    trace[Meta.Tactic.if_pull] s!"if_pull: \n{← ppExpr e}\n==>\n{← ppExpr e'}\n"
    return .visit { expr := e', proof? := prf }

  | _ => return .continue



-- #check ((if 0 < 1 then (fun x : Float => x + 2) else (fun x : Float => x + 3)) 42).log rewrite_by
--   simp only [if_pull]

-- #check (let y := 5;  ((if 0 < 1 then (fun x : Float => x + 2 + y) else (fun x : Float => x + 3 + y)) 42).log) rewrite_by
--   simp (config:={zeta:=false}) only [if_pull]
