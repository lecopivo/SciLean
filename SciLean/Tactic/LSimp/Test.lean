import SciLean.Tactic.LSimp.Elab
import SciLean.Util.RewriteBy
import SciLean.Core

import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts

open Lean ProofWidgets Recharts


-- def plot (x y : Array Float) : Html :=

open scoped ProofWidgets.Jsx in
def plot (data : Array (Float×Float)) : Html := Id.run do

  let mut jsonData : Array Json := #[]
  for (x,y) in data do
    jsonData := jsonData.push (json% {x: $(toJson x) , y: $(toJson y), z: $(toJson (y/2))});

  <p>
  <LineChart width={400} height={400} data={jsonData}>
    <XAxis dataKey?="x" />
    <YAxis />
    <Line type={.step} dataKey="y" stroke="#8884d8" dot?={Bool.false} />
    <Line type={.linear} dataKey="z" stroke="#8884d8" dot?={Bool.false} />
  </LineChart>
  </p>

#html plot #[(1,1),(2,4),(3,9),(5,25)]

open SciLean Lean Meta Qq

set_default_scalar Float


inductive ExprType where
  | v1 | v2 | v3

def testExpressionAux (n : Nat) (k : Array Expr → MetaM α) (t : ExprType := .v1) : MetaM α := do
  match n with
  | 0 =>
    withLocalDeclD `x q(Float) fun x => k #[x]
  | n+1 =>
    testExpressionAux n fun xs => do
      let val ←
        match t with
        | .v1 =>
          mkAppFoldlM ``HMul.hMul xs
        | .v2 =>
          if xs.size == 1 then
            mkAppFoldlM ``HMul.hMul #[xs[0]!, xs[0]!]
          else
            mkAppFoldlM ``HMul.hMul xs[xs.size-2:xs.size]
        | .v3 =>
          if xs.size == 1 then
            mkAppFoldlM ``HMul.hMul #[xs[0]!, xs[0]!]
          else
            mkAppFoldlM ``HMul.hMul #[xs[xs.size-1]!, xs[0]!]
      withLetDecl ((`x).appendAfter (toString n)) q(Float) val fun x => do
        k (xs.push x)


def testExpression (n : Nat) : MetaM Q(Float → Float) :=
  testExpressionAux n (fun xs => mkLambdaFVars xs xs[xs.size-1]!)


#eval show MetaM Unit from do
  IO.println (← ppExpr (← testExpression 8))


#check (0 + 1 + 0) rewrite_by lsimp


structure MeasureData where
  time : Aesop.Nanos
  numSteps : Nat

open SciLean.Tactic.LSimp
def callLSimpData (e : Expr) : MetaM (Expr×MeasureData) := do

  let stateRef : IO.Ref Simp.State ← IO.mkRef {}

  let mut simprocs : Simp.Simprocs := {}
  simprocs ← simprocs.add ``Mathlib.Meta.FunTrans.fun_trans_simproc false
  let r := (lsimp e).run
   (Simp.mkDefaultMethodsCore #[simprocs]) {config:={zeta:=false,singlePass:=false},simpTheorems:=#[←getSimpTheorems]} stateRef

  let (e,t) ← Aesop.time <| r.runInMeta (fun r => mkLambdaFVars r.vars r.expr)


  return (e, { time := t, numSteps := (← stateRef.get).numSteps })



def measureOnTestExpression (n : Nat) : MetaM (Array MeasureData) := do



  for i in [0:n] do
    let e := q(cderiv Float $(← testExpression i))
    let (e',data) ← callLSimpData e

    IO.println s!"{← ppExpr e}\n==>\n{← ppExpr e'}\n"


  return #[]



#eval show MetaM Unit from do
  let _ ← measureOnTestExpression 10

set_option trace.Meta.Tactic.fun_trans true
set_option trace.Meta.Tactic.fun_trans.step true

#check (cderiv Float (fun x : Float => x * x)) rewrite_by lsimp; lsimp


#check (cderiv Float (fun x : Float => let x1 := x * x; x1*x1))
         rewrite_by fun_trans (config:={zeta:=false}) [Tactic.lift_lets_simproc]
