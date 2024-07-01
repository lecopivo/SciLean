import SciLean.Tactic.MathlibCompiledTactics
import SciLean.Tactic.LSimp.Elab
import SciLean.Util.RewriteBy
import SciLean.Core

import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts

open Lean ProofWidgets Recharts


variable (x y : ℤ)

open Lean Meta Simp
simproc_decl mySimpMatch (_) := fun e => do
  if let .reduced e ← reduceMatcher? e then
    return .visit { expr := e}
  return .continue

set_option trace.Meta.Tactic.simp.cache true in

-- unletNum
-- unletIf
-- unletFun
-- unletCtor
-- unletFVar
-- unletBVar
-- unletBVar

-- set_option pp.raw true in
#check ((1*x) + (1*x) + (1*x) + (1*x)  + (1*x)  + (1*x)  + (1*x)  + (1*x)) rewrite_by lsimp --(config:={zeta:=false})


def id' {α} (a : α) := a


#check (let_fun foo := (fun z (h : x = z) => x + x); x + x + foo x sorry) rewrite_by lsimp (config:={contextual:=true})


#check (if h : x = y then x + x else x * x) rewrite_by lsimp (config:={contextual:=true})


#exit
#check (fun (z : ℤ) (h : x = z) =>
        x + x) rewrite_by enter [z,h]; lsimp (config:={contextual:=true})


#check (let (a,b) := (x+(y+0), x*y+(y+0)); a + b) rewrite_by lsimp --(config:={zeta:=false})

-- set_option trace.Meta.Tactic.simp true
set_option trace.Meta.Tactic.simp.discharge true

#check (let a := if x ≤ 0 then (y*y, fun z => z*z) else (y+y, fun z => z + z); a.2 a.1) rewrite_by lsimp only

#exit

set_option trace.Meta.Tactic.simp.heads true
set_option trace.Meta.Tactic.simp.proj true

set_option trace.Meta.Tactic.simp.rewrite true in

#check (let (a,b) := (x+y, x*y); a + b) rewrite_by lsimp (config := {iota:=false}) only [mySimpMatch]


variable (w : ℤ×ℤ)
#check (let (a,b) := w; a + b) rewrite_by lsimp (config := {iota:=false}) only [mySimpMatch]


#exit

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
  let lcacheRef : IO.Ref Tactic.LSimp.Cache ← IO.mkRef {}

  let mut simprocs : Simp.Simprocs := {}
  simprocs ← simprocs.add ``Mathlib.Meta.FunTrans.fun_trans_simproc false
  let r := (lsimp e).run
   (Simp.mkDefaultMethodsCore #[simprocs]) {config:={zeta:=false,singlePass:=false},simpTheorems:=#[←getSimpTheorems]} ⟨lcacheRef, stateRef⟩

  let (e,t) ← Aesop.time <| r.runInMeta (fun (r,_) => mkLambdaFVars r.vars r.expr)


  return (e, { time := t, numSteps := (← stateRef.get).numSteps })



def measureOnTestExpression (n : Nat) : MetaM (Array MeasureData) := do



  for i in [0:n] do
    let e := q(cderiv Float $(← testExpression i))
    let (e',data) ← callLSimpData e

    IO.println s!"{← ppExpr e}\n==>\n{← ppExpr e'}\n"


  return #[]



-- -- #eval show MetaM Unit from do
-- --   let _ ← measureOnTestExpression 4

-- -- set_option trace.Meta.Tactic.fun_trans true
-- -- set_option trace.Meta.Tactic.fun_trans.step true

-- set_option trace.Meta.Tactic.simp.heads true

-- #check (let a := 1; let b := a + 1; b) rewrite_by lsimp

-- #check (let a :=
--           let c := 1
--           let d := c + 3
--           c + d + 2
--         let b := a + 5
--         a + b) rewrite_by lsimp

-- example :
--   (let a := (let c := 1; let d := c + 3;  c + d + 2); let b := a + 5; a + b)
--   =
--   19 := by (conv => lhs; lsimp)


----------------------------------------------------------------------------------------
-- Tests -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

-- set_option trace.Meta.Tactic.simp.heads true

example (n : Nat) :
  n
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
  (let a := 1; a + n)
  =
  (1 + n) := by (conv => lhs; lsimp)

example (n : Nat) :
  (0 + n)
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
  (0 + 1 * n)
  =
  n := by (conv => lhs; lsimp)

example (n : Nat) :
  (let a := (0 + 1 * n); a)
  =
  n := by (conv => lhs; lsimp)

example (a : ℤ) :
   (if 0 ≤ 0 + a then 1 else 0)
   =
   (if 0 ≤ a then 1 else 0) := by conv => lhs; lsimp

example (n : Nat) :
    (let a :=
       let c := 0 + n
       let d := c + 0 + 3
       c + d + 1 * n + 2
     let b := a + 5
     a + b)
    =
    n + (n + 3) + n + 2 + (n + (n + 3) + n + 2 + 5) := by
  (conv => lhs; lsimp)

example (n : Nat) (i : Fin n) :
    (let j := 2*i.1
     let hj : j < 2*n := by omega
     let j : Fin (2*n) := ⟨j, hj⟩
     let k :=
       let a := j + j
       a + j
     j + k)
    =
    let j := 2*i.1
    let hj : j < 2*n := by omega
    let j : Fin (2*n) := ⟨j, hj⟩
    (j + (j + j + j)) := by
  (conv => lhs; lsimp)

-- tests under lambda binder

example :
  (fun n : Nat => n)
  =
  (fun n : Nat => n) := by (conv => lhs; lsimp)


example :
  (fun n => let a := 1; a + n)
  =
  (fun n => 1 + n) := by (conv => lhs; lsimp)


example :
  (fun n => let a := (0 + 1 * n); a)
  =
  (fun n => n) := by (conv => lhs; lsimp)


example :
    (fun n : Nat=>
     let c := n
     let a := c + 1 * n
     a)
    =
    (fun n => n + n) := by
  (conv => lhs; lsimp)
