import SciLean.Tactic.LSimp.Main
import SciLean.Core

namespace SciLean.Tactic.LSimp

open Lean Elab Tactic
open TSyntax.Compat

open Lean Meta


open Lean.Parser.Tactic
syntax (name := Parser.lsimp) "lsimp" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic


def callLSimpAux (e : Expr) (k : Expr → Expr → Array Expr → MetaM α) : MetaM α := do

  let stateRef : IO.Ref Simp.State ← IO.mkRef {}
  let lcacheRef : IO.Ref Cache ← IO.mkRef {}

  let mut simprocs : Simp.Simprocs := {}
  simprocs ← simprocs.add ``Mathlib.Meta.FunTrans.fun_trans_simproc false
  let .some ext ← getSimpExtension? `ftrans_simp | throwError "can't find theorems!"
  let thms ← ext.getTheorems
        >>= (·.addDeclToUnfold ``scalarGradient)
        >>= (·.addDeclToUnfold ``scalarCDeriv)

  let r :=
    (lsimp e).run
      (Simp.mkDefaultMethodsCore #[simprocs])
      {config:={zeta:=false,singlePass:=false},simpTheorems:=#[thms]}
      ⟨lcacheRef, stateRef, {}⟩

  let (a,t) ← Aesop.time <| r.runInMeta (fun (r,s) => do
    trace[Meta.Tactic.simp.numSteps] "{(← stateRef.get).numSteps}"
    s.printTimings

    -- IO.println "cache"
    -- (← s.simpState.get).cache.forM fun e v => do
    --   IO.println s!"{← ppExpr e}"

    k r.expr (← r.getProof) r.vars)

  trace[Meta.Tactic.simp.time] "lsimp took {t.printAsMillis}"

  return a


def callLSimp (e : Expr) : MetaM (Expr×Expr) := do
  callLSimpAux e (fun e prf vars => do
    return (← mkLambdaFVars vars e, ← mkLambdaFVars vars prf))



open Lean.Parser.Tactic in
syntax (name:=lsimp_conv) "lsimp" /-(config)? (discharger)? (normalizer)?-/ : conv


open Lean Elab Tactic in
@[tactic lsimp_conv] unsafe def lsimpConv : Tactic := fun _ => do
  let e ← Conv.getLhs
  let (e',prf) ← callLSimp e
  Conv.updateLhs e' prf
