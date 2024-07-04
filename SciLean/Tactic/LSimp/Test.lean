import SciLean.Tactic.MathlibCompiledTactics
import SciLean.Tactic.LSimp.Elab
import SciLean.Util.RewriteBy
import SciLean.Core

import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts

open Lean ProofWidgets Recharts


-- inductive ExprType where
--   | v1 | v2 | v3

-- def testExpressionAux (n : Nat) (k : Array Expr → MetaM α) (t : ExprType := .v1) : MetaM α := do
--   match n with
--   | 0 =>
--     withLocalDeclD `x q(Float) fun x => k #[x]
--   | n+1 =>
--     testExpressionAux n fun xs => do
--       let val ←
--         match t with
--         | .v1 =>
--           mkAppFoldlM ``HMul.hMul xs
--         | .v2 =>
--           if xs.size == 1 then
--             mkAppFoldlM ``HMul.hMul #[xs[0]!, xs[0]!]
--           else
--             mkAppFoldlM ``HMul.hMul xs[xs.size-2:xs.size]
--         | .v3 =>
--           if xs.size == 1 then
--             mkAppFoldlM ``HMul.hMul #[xs[0]!, xs[0]!]
--           else
--             mkAppFoldlM ``HMul.hMul #[xs[xs.size-1]!, xs[0]!]
--       withLetDecl ((`x).appendAfter (toString n)) q(Float) val fun x => do
--         k (xs.push x)


-- def testExpression (n : Nat) : MetaM Q(Float → Float) :=
--   testExpressionAux n (fun xs => mkLambdaFVars xs xs[xs.size-1]!)

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



variable (a b : Nat)


/--
info: let u := 1 + a;
let w := a + b;
fun x =>
let v := u + x;
fun y =>
let p := y * y;
u + v + w + p : ℕ → ℕ → ℕ
-/
#guard_msgs in
#check
  (fun (x y : Nat) =>
    let p := y * y
    let u := 1 + a;
    let v := u + x;
    let w := a + b;
    u + v + w + p) rewrite_by lsimp


variable (x y : Nat)


-- this tests if cache is working properly as we rewrite `x ==> z` using `_h` but then `_h` and `z`
-- goes out of scope
/--
info: let_fun foo := fun z _h => z + z;
x + x + foo x ⋯ : ℕ
-/
#guard_msgs in
#check (let_fun foo := (fun z (_h : x = z) => x + x); x + x + foo x rfl)
  rewrite_by
    lsimp (config:={contextual:=true})



-- #check (fun (z : Nat) (h : x = z) =>
--         x + x) rewrite_by enter [z,h]; lsimp (config:={contextual:=true})


-- todo: add option to split `let _ := if ...` and test this out
-- #check (let a := if x ≤ 0 then (y*y, fun z => z*z) else (y+y, fun z => z*z); a.2 a.1) rewrite_by lsimp only


-- todo deal with pattens in let bindings
-- /-- info: let a := x + y
-- let b := x*y
-- a + b : ℕ -/
-- #guard_msgs in
-- #check (let (a,b) := (x+y, x*y); a + b) rewrite_by lsimp
