import SciLean.Tactic.LSimp.Main

namespace SciLean.Tactic.LSimp

open Lean Elab Tactic
open TSyntax.Compat

open Lean Meta


def callLSimpAux (e : Expr) (k : Expr → Expr → Array Expr → MetaM α) : MetaM α := do

  let stateRef : IO.Ref Simp.State ← IO.mkRef {}
  let lcacheRef : IO.Ref Cache ← IO.mkRef {}

  let mut simprocs : Simp.Simprocs := {}
  simprocs ← simprocs.add ``Mathlib.Meta.FunTrans.fun_trans_simproc false
  let r :=
    (lsimp e).run
      (Simp.mkDefaultMethodsCore #[simprocs])
      {config:={zeta:=false,singlePass:=false},simpTheorems:=#[←getSimpTheorems]}
      ⟨lcacheRef, stateRef⟩

  let a ← r.runInMeta (fun (r,_) => do
    k r.expr (← r.getProof) r.vars)

  trace[Meta.Tactic.simp.steps] "lsimp took {(← stateRef.get).numSteps} steps"

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


@[export scilean_lsimp_compile_test]
def compileCheckImpl : IO Unit := do
  IO.println "running compiled code!"


@[export scilean_lsimp_compile_test_2]
def compileCheckImpl2 : IO Unit := do
  SciLean.Tactic.LSimp.compileCheck
