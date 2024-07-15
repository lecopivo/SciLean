import SciLean.Core.Rand
import SciLean.Util.RewriteBy
import SciLean.Tactic.InferVar

open Lean

set_option linter.unusedVariables false

namespace SciLean.Rand

inductive Trace where
| nil
| single (tag : Name) (T : Type)
| pair (t s : Trace)

instance : Append Trace := ⟨fun t s => .pair t s⟩

def Trace.type : (trace : Trace) → Type
  | .nil => Unit
  | .single n T => T
  | .pair t s => t.type × s.type

def Trace.tags : (trace : Trace) → List Name
  | .nil => []
  | .single n _ => [n]
  | .pair t s => t.tags ++ s.tags

structure RandWithTrace (X : Type) (trace : Trace) (T : Type) where
  rand : Rand X
  traceRand : Rand T
  map : T → X
  hmap : traceRand.map map = rand
  htype : T = trace.type

def return' (x : X) : RandWithTrace X .nil Unit where
  rand := Pure.pure x
  traceRand := Pure.pure ()
  map := fun _ => x
  hmap := by simp
  htype := rfl

def RandWithTrace.bind (x : RandWithTrace X t T) (f : X → RandWithTrace Y s S)
    (hinter : t.tags.inter s.tags = [] := by simp[Trace.tags,List.inter]; done) : RandWithTrace Y (t++s) (T×S) where
  rand := x.rand >>= (fun x' => (f x').rand)
  traceRand := do
    let tx ← x.traceRand
    let x := x.map tx
    let ty ← (f x).traceRand
    pure (tx,ty)
  map  := fun (wx,wy) => (f (x.map wx)).map wy
  hmap := by simp; sorry_proof
  htype := by
    simp[Trace.type]
    rw[← x.htype]
    -- how do I get element of `X` in this proof to invoke `(f x).htype`?
    -- I can probably do case on `Nonempty X`
    rw[← (f sorry).htype]

def sample {X} (x : Rand X) (tag : Name) :
    RandWithTrace X (.single tag X) X where
  rand := x
  traceRand := x
  map := fun x => x
  hmap := by simp[Rand.map]
  htype := rfl

@[simp]
theorem sample_map (x : Rand X) (tag : Name) :
    (sample x tag).map = fun x => x := by rfl

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
  let X := (← inferType x').appFn!.appFn!.appArg!
  let Y ← mkFreshTypeMVar
  let f ← elabTermAndSynthesize (← `(fun $x => $b)) (← mkArrow X Y)
  let fx ← mkAppM ``RandWithTrace.bind #[x',f]
  let (xs,_,_) ← forallMetaTelescope (← inferType fx)
  try synthesizeAutoArg xs[0]!
  catch _ => throwError "traces contain repeated variable"
  -- synthesizeAutoArg xs[2]!
  return mkAppN fx xs
  | _ => throwUnsupportedSyntax


def test1 :=
  let x <~ sample (flip 0.5) `v1
  return' x


def test2 :=
  let x <~ sample (flip 0.5) `v1
  let y <~ sample (normal 0.1 (x.toNat.toFloat)) `v2
  let z <~ sample (uniform (Set.Icc y (2*y))) `v3
  return' (x.toNat.toFloat+y+z)


#eval test2.rand.get
#eval test2.traceRand.get
#eval do pure (test2.map (← test2.traceRand.get))


variable {R} [RealScalar R]
open MeasureTheory

theorem trace_bind_pdf (x : RandWithTrace X t T) (f : X → RandWithTrace Y s S)
  (h : t.tags.inter s.tags = [] := by simp[Trace.tags,List.inter])
  [MeasureSpace S] [MeasureSpace T] :
  ((x.bind f h).traceRand).pdf R
  =
  fun (wt,ws) =>
    let xpdf := x.traceRand.pdf R volume wt
    let x' := x.map wt
    let fxpdf := (f x').traceRand.pdf R volume ws
    xpdf * fxpdf := by sorry_proof


@[simp]
theorem trace_return_pdf (x : X) [MeasureSpace X] :
  (return' x).traceRand.pdf R volume
  =
  fun x => 1 := sorry_proof


@[simp]
theorem trace_sample_pdf (x : Rand X) (n : Name) [MeasureSpace X] :
  (sample x n).traceRand.pdf R volume
  =
  fun x' => x.pdf R volume x' := sorry_proof


#check ((sample (normal (0.0:Float) 1.0) `v1).traceRand.pdf Float)
  rewrite_by
    simp


set_option trace.Meta.Tactic.simp.unify true
set_option trace.Meta.Tactic.simp.discharge true

#check ((let x <~ sample (normal (0.0:Float) 1.0) `v1; return' x).traceRand.pdf Float)
  rewrite_by
    simp[trace_bind_pdf]


set_option pp.funBinderTypes true

#check (
    (let x <~ sample (normal (0.0:Float) 1.0) `v1
     let y <~ sample (normal x 1.0) `v2
     return' (x*y)).traceRand.pdf Float)
  rewrite_by
    simp[trace_bind_pdf]
