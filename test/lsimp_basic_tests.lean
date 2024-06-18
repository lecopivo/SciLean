import SciLean.Tactic.LSimp.Elab
import SciLean.Util.RewriteBy
import SciLean.Core
import SciLean.Tactic.MathlibCompiledTactics
import SciLean.Util.Profile


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
  (fun n => let a := (0 + 1 * n * 1 * 2); a)
  =
  (fun n => n * 2) := by (conv => lhs; lsimp)


example :
    (fun n : Nat=>
     let c := n
     let a := c + 1 * n
     a)
    =
    (fun n => n + n) := by
  (conv => lhs; lsimp)


example :
    (fun (n : Nat) (i : Fin n) =>
     let j := 2*i.1
     let hj : j < 2*n := by omega
     let j : Fin (2*n) := ⟨j, hj⟩
     let k :=
       let a := j + j
       a + j
     j + k)
    =
    fun (n : Nat) (i : Fin n) =>
    let j := 2*i.1
    let hj : j < 2*n := by omega
    let j : Fin (2*n) := ⟨j, hj⟩
    (j + (j + j + j)) := by
  (conv => lhs; lsimp)




set_default_scalar Float

open SciLean

-- set_option trace.Meta.Tactic.simp.numSteps true
-- set_option trace.Meta.Tactic.simp.time true


-- -- set_option trace.Meta.Tactic.simp.proj true
-- set_option trace.Meta.Tactic.simp.steps true


open Lean Meta Elab Term Tactic Conv in
elab "timeTactic" t:conv : conv => do

  let target ← getMainTarget
  let ((targetNew, proof),time) ← Aesop.time <| convert target (withTacticInfoContext (← getRef) (evalTactic t))
  liftMetaTactic1 fun mvarId => mvarId.replaceTargetEq targetNew proof
  IO.println s!"tactic {t.raw.prettyPrint} took {time.printAsMillis}"


#check (∇ x : Float, let y := x * x; x * y)
  rewrite_by
    unfold scalarGradient
    lsimp only [Mathlib.Meta.FunTrans.fun_trans_simproc, ftrans_simp]


macro "lautodiff" : conv =>
  `(conv| (unfold scalarGradient scalarCDeriv;
           lsimp (config := {zeta:=false}) only
             [Mathlib.Meta.FunTrans.fun_trans_simproc, ftrans_simp]))

-- set_option trace.Meta.Tactic.fun_trans true in

-- #check (∇ (x : Float×Float), let y := x + x; let z := x + y; y.1*z.2)
--   rewrite_by
--     unfold scalarGradient
--     timeTactic autodiff

-- #check (∇ (x : Float×Float), let y := x + x; let z := x + y; y.1*z.2)
--   rewrite_by
--     unfold scalarGradient
--     timeTactic lsimp

-- set_option trace.Meta.Tactic.fun_trans true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.rewrite true in
#check (∇ x : Float,
          let x1 := x * x
          let x2 := x * x1
          let x3 := x * x2
          let x4 := x * x3
          let x5 := x * x4
          let x6 := x * x5
          -- let x7 := x * x6
          -- let x8 := x * x7
          -- let x9 := x * x8
          -- let x10 := x * x9
          -- let x11 := x * x10
          x6)
  rewrite_by
    unfold scalarGradient scalarCDeriv
    lautodiff


#check (∂ x : Float, let y := x * x; x * y)
  rewrite_by
    lautodiff


#check (∂> x : Float, let y := x * x; x * y)
  rewrite_by
    lautodiff


-- #check Nat

#check (∂> x : Float, let y := x * x; let z := x * y; x * y * z)
  rewrite_by
    lautodiff

set_option profiler true

set_option trace.Meta.Tactic.simp.numSteps true
set_option trace.Meta.Tactic.simp.time true
-- set_option trace.Meta.Tactic.simp.proj true
-- set_option trace.Meta.Tactic.simp.heads true
-- set_option trace.Meta.Tactic.simp.cache true

set_default_scalar Float

open SciLean


#check (structProj 1 ())
  rewrite_by
    unfold scalarGradient
    lautodiff
    lautodiff



-- #check (∇ x : Float, let y := x * x; let z := x * y; x * y * z)
--   rewrite_by
--     unfold scalarGradient
--     lautodiff
--     lautodiff-- 16107 steps & 4.45s | with cache: 1295 steps && 709ms


-- #check (∇ x : Float, let y := x * x; let z := x * y; x * y * z)
--   rewrite_by
--     unfold scalarGradient
--     lautodiff -- 16107 steps & 4.45s | with cache: 1295 steps && 709ms


#check (∇ x : Float,
          let x1 := x * x
          let x2 := x1 * x1
          let x3 := x2 * x2
          let x4 := x3 * x3
          let x5 := x4 * x4
          let x6 := x5 * x5
          -- let x8 := x * x7
          -- let x9 := x * x8
          -- let x10 := x * x9
          -- let x11 := x * x10
          x6)
  rewrite_by
    unfold scalarGradient
    lautodiff




#check (∇ x : Float,
          let x1 := x * x
          let x2 := x * x1
          let x3 := x * x2
          let x4 := x * x3
          let x5 := x * x4
          let x6 := x * x5
          -- let x8 := x * x7
          -- let x9 := x * x8
          -- let x10 := x * x9
          -- let x11 := x * x10
          x6)
  rewrite_by
    unfold scalarGradient
    lautodiff



#check (∇ x : Float,
          let x1 := x * x
          let x2 := x * x1
          let x3 := x * x2
          let x4 := x * x3
          let x5 := x * x4
          let x6 := x * x5
          -- let x8 := x * x7
          -- let x9 := x * x8
          -- let x10 := x * x9
          -- let x11 := x * x10
          x6)
  rewrite_by
    unfold scalarGradient
    lautodiff




-- #check (∂> x : Float,
--           let x1 := x * x
--           let x2 := x * x1
--           let x3 := x * x2
--           let x4 := x * x3
--           let x5 := x * x4
--           let x6 := x * x5
--           let x7 := x * x6
--           let x8 := x * x7
--           let x9 := x * x8
--           let x10 := x * x9
--           let x11 := x * x10
--           x10 * x11)
--   rewrite_by
--     unfold scalarGradient
--     lautodiff





#exit


#check (∇ x : Float,
          let x1 := x * x
          let x2 := x * x1
          let x3 := x * x2
          let x4 := x * x3
          x3 * x4)
  rewrite_by
    unfold scalarGradient
    lautodiff
    simp


#exit

#check (∇ x : Float,
          let x1 := x * x
          let x2 := x * x1
          let x3 := x * x2
          let x4 := x * x3
          let x5 := x * x4
          x * x1 * x2 * x3 * x4 * x5)
  rewrite_by
    unfold scalarGradient
    lautodiff



#check (∇ x : Float,
          let x1 := x * x
          let x2 := x * x1
          let x3 := x * x2
          let x4 := x * x3
          let x5 := x * x4
          x * x1 * x2 * x3 * x4 * x5)
  rewrite_by
    unfold scalarGradient
    autodiff
