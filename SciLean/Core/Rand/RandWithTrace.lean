import SciLean.Core.Rand
import SciLean.Util.RewriteBy
import SciLean.Tactic.InferVar

open Lean

set_option linter.unusedVariables false

namespace SciLean.Rand

inductive Trace where
| list (l : List (Name×Type))

def Trace.append (t s : Trace) : Trace :=
  match t, s with
  | .list t, .list s => .list (t ++ s)

open Classical in
def Trace.type (trace : Trace) : Type :=
  match trace with
  | .list [] => Unit
  | .list [(_,T)] => T
  | .list ((_,t)::tr) => t × (Trace.list tr).type

def Trace.tags (trace : Trace) : List Name :=
  match trace with
  | .list [] => []
  | .list ((n,_)::tr) => n :: (Trace.list tr).tags

def Trace.appendIso {t s : Trace} : (t.append s).type ≃ t.type × s.type := sorry

structure RandWithTrace (X : Type) (trace : Trace) where
  rand : Rand X
  r : Rand trace.type
  map : trace.type → X

def return' (x : X) : RandWithTrace X (.list []) where
  rand := Pure.pure x
  r := Pure.pure (Eq.mp (by simp[Trace.type]) ())
  map := fun _ => x

def RandWithTrace.bind (x : RandWithTrace X t) (f : X → RandWithTrace Y s)
    (hinter : t.tags.inter s.tags = [] := by simp[Trace.tags,List.inter]; done)
    {tr} (hu : tr = t.append s := by simp[Trace.append]; infer_var) : RandWithTrace Y tr where
  r := do
    let xr ← x.r
    let x := x.map (← x.r)
    let yr ← (f x).r
    let t := Trace.appendIso.symm (xr,yr)
    pure (hu ▸ t)
  rand := x.rand >>= (fun x' => (f x').rand)
  map s :=
    let (sx,sy) := Trace.appendIso (hu▸s)
    (f (x.map sx)).map sy

def sample {X} (x : Rand X) (tag : Name) :
    RandWithTrace X (.list [(tag,X)]) where
  rand := x
  r := Eq.mp (by simp[Trace.type]) x
  map := fun x => (x rewrite_type_by simp[Trace.type])

open Lean.Parser Term in
syntax (name:=probStx) withPosition("let" funBinder " <~ " term (semicolonOrLinebreak ppDedent(ppLine) term)?) : term

open Lean Elab Term Meta Qq

unsafe def synthesizeAutoArg (e : Expr) : TermElabM Unit := do
  unless e.isMVar do throwError "expecting mvar"
  let E ← e.mvarId!.getType
  unless E.isAppOfArity ``autoParam  2 do
    throwError "expecting mvar of tyep `autoParam _ _`"
  let stx  ← evalExpr Syntax q(Syntax) E.appArg!
  let stx : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨stx⟩
  try runTactic e.mvarId! (← `(term| by unfold autoParam; ($stx:tacticSeq))) false
  catch _ => pure ()
  unless ← e.mvarId!.isAssigned do
    throwError "failed to fill auto parameter {← ppExpr E}"


@[term_elab probStx]
unsafe def probStxElab : TermElab := fun stx _ =>
  match stx with
  | `(let $x <~ $y; $b) => do
  let x' ← elabTermAndSynthesize y none
  let X := (← inferType x').appFn!.appArg!
  let Y ← mkFreshTypeMVar
  let f ← elabTermAndSynthesize (← `(fun $x => $b)) (← mkArrow X Y)
  let fx ← mkAppM ``RandWithTrace.bind #[x',f]
  let (xs,_,_) ← forallMetaTelescope (← inferType fx)
  try synthesizeAutoArg xs[0]!
  catch _ => throwError "traces contain repeated variable"
  synthesizeAutoArg xs[2]!
  return mkAppN fx xs
  | _ => throwUnsupportedSyntax


def test1 :=
  let x <~ sample (flip 0.5) `v1
  let y <~ sample (normal 0.1 0.3) `v2
  let z <~ sample (uniform (Set.Icc 0.1 0.3)) `v3
  return' (x,y,z)

def test2 :=
  let x <~ sample (flip 0.5) `a
  let y <~ sample (normal 0.1 0.3) `b
  let z <~ sample (uniform (Set.Icc 0.1 0.3)) `c
  return' (x,y,z)

def test3 :=
  let t1 <~ test1
  let t2 <~ test2
  return' (t1+t2)

#check test1
#check test2
#check test3

-- def invalid1 :=
--   let x <~ sample (flip 0.5) `a
--   let y <~ sample (normal 0.1 0.3) `a
--   return' (x,y)

-- def invalid2 :=
--   let x <~ test1
--   let y <~ test1
--   return' (x+y)
