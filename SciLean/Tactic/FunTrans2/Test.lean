import SciLean.Tactic.FunTrans2.Core
import SciLean.Core
import SciLean.Lean.Meta.Basic



set_default_scalar Float

open Lean Meta Qq SciLean


-- set_option trace.Meta.Tactic.fun_trans2 true
-- set_option trace.Meta.Tactic.fun_trans2.fun_trans true
-- set_option trace.Meta.Tactic.fun_trans2.quick true
-- set_option trace.Meta.Tactic.fun_trans true
set_option profiler true

def expression1Aux (n : Nat) (k : Array Expr → MetaM α) : MetaM α := do
  match n with
  | 0 =>
    withLocalDeclD `x q(Float) fun x => k #[x]
  | n+1 =>
    expression1Aux n fun xs => do
      let val ← mkAppFoldlM ``HMul.hMul xs[xs.size-3:xs.size-1]
      -- -- let val ← mkAppFoldlM ``HMul.hMul #[xs[xs.size-1]!,xs[xs.size-1]!]
      -- let val ← mkAppFoldlM ``HMul.hMul xs
      withLetDecl ((`x).appendAfter (toString n)) q(Float) val fun x => do
        k (xs.push x)

def expression1 (n : Nat) : MetaM Q(Float → Float) :=

  expression1Aux n (fun xs => mkLambdaFVars xs xs[xs.size-1]!)

#eval show MetaM Unit from do

  withLocalDeclQ `x default q(Float) fun x => do
  withLocalDeclQ `dx default q(Float) fun dx => do


  let mut ts : Array Float := #[]

  for i in [0:30] do

    let e ← expression1 i

    let e := q((revDeriv Float $e $x).2 $dx)

    let (r,time) ← Aesop.time (callFunTrans2 e)

    -- let (((e'',_),_),time') ← Aesop.time <| elabConvRewrite e #[] (← `(conv| autodiff)) |>.run {} {}

    -- (Elab.Term.elabTerm (←`(((revDeriv Float $e 1.0).2 0.1) rewrite_by autodiff) none).run {} {}

    let e' ← r.toExpr
    IO.println s!"{← ppExpr e}\n"
    IO.println s!"fun_trans2 result is:\n\n{← ppExpr e'}\n"
    -- IO.println s!"autodiff result is:\n\n{← ppExpr e''}\n"
    IO.println s!"fun_trans2 took {time.printAsMillis}\n"
    -- IO.println s!"autodiff took {time'.printAsMillis}\n"
    IO.println "-------------------------------------------------------"


-- yᵢ = b * xᵢ^a
-- ∑ i, (log yᵢ - a * log xᵢ + log b)^2



#exit

#eval show MetaM Unit from do


  let e := q(let t1 :=
               let a1 := 1 + (let b := 1+2; b + 4)
               let a2 := a1 + a1
               a1 * a2
             let t2 := 0 + t1 + 4
             let t3 := t2 * t1 + 0 + t1
             let t4 := t2 * t1 + 0 + t1 + t3
             let foo := fun x : Nat => x + x
             t1 + t2 + foo t3 + t4)


  let e := q(let t := (1+1, 1+1,1+1)
             t)


  let e := q(let x := 0.1
             let t1 := SciLean.fwdDeriv Float (fun x => x*x*x*x*x*x) x 1
             let t2 := (revDeriv Float (fun x => x*x*x*x) t1.1).2 x
             let t3 := (revDeriv Float (fun x => let y := x*x; x*x*y*x*x) t1.1).2 x
             t1.2 * t2 * t3)


  let e := q((revDeriv Float (fun x => let y := x*x; let z := x * y; x*x*y*x*x*z*z*x*x*z) 0.4).2 0.1)


  -- let e := q(let t2 := (revDeriv Float (fun x => x*x) 0.1).2 0.3
  --            t2)


  -- let e := q((5.0 + 5.0, fun dy =>
  --             let dx := (5.0, fun dx => dx).2 dy;
  --             (5.0, fun dx' dx => dx + dx').2 dy dx).2 1)


  -- let e := q((<∂ x:=5.0, ( x*x*x*x*x*x*x*x)).2 1)

  -- let e := q((<∂ x:=5.0, (x * x)))

  -- let e := q((∂> x:=5.0+2.0;1+2, (x * x * x)))

  -- let e := q((0.1, fun dx' dx : Float => dx + dx').2 1 2)


  let insts ← getLocalInstances
  let (r,time) ← Aesop.time (funTrans2 (← getLCtx) insts e)

  let e' ← r.toExpr
  IO.println s!"result is:\n\n{← ppExpr e'}\n"
  IO.println s!"fun_trans2 took {time.printAsMillis}\n"
