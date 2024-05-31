import SciLean.Tactic.LSimp.Main

namespace SciLean.Tactic.LSimp

open Lean Elab Tactic
open TSyntax.Compat

open Lean Meta


def callLSimpAux (e : Expr) (k : Expr → Expr → Array Expr → MetaM α) : MetaM α := do

  let stateRef : IO.Ref Simp.State ← IO.mkRef {}

  let mut simprocs : Simp.Simprocs := {}
  simprocs ← simprocs.add ``Mathlib.Meta.FunTrans.fun_trans_simproc false
  let r := (lsimp e).run
   (Simp.mkDefaultMethodsCore #[simprocs]) {config:={zeta:=false,singlePass:=false},simpTheorems:=#[←getSimpTheorems]} stateRef

  let a ← r.runInMeta (fun r =>
    k r.expr (r.proof?.getD default) r.vars)

  return a


def callLSimp (e : Expr) : MetaM Expr := do
  callLSimpAux e (fun e _ vars => do
    mkLambdaFVars vars e)



open Lean.Parser.Tactic in
syntax (name:=lsimp_conv) "lsimp" /-(config)? (discharger)? (normalizer)?-/ : conv


open Lean Elab Tactic in
@[tactic lsimp_conv] unsafe def lsimpConv : Tactic := fun _ => do
  let e ← Conv.getLhs
  let e' ← callLSimp e
  Conv.updateLhs e' (← mkAppM ``sorryAx #[← mkEq e e', .const ``Bool.false []])
