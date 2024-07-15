import SciLean.Core.Rand
import SciLean.Util.RewriteBy
import SciLean.Tactic.InferVar

open Lean

set_option linter.unusedVariables false

namespace SciLean.Rand

inductive Trace where
| nil
| cons (tag : Name) (T : Type) (tail : Trace)

protected def Trace.append : (t s : Trace) → Trace
  | .nil,    s => s
  | .cons n T ts, s => .cons n T (Trace.append ts s)

instance : Append Trace := ⟨fun t s => t.append s⟩

-- open Classical in
def Trace.type : (trace : Trace) → Type
  | .nil => Unit
  -- | .cons n T .nil => T -- this case would be nice but makes all the proofs more compilicated
  | .cons n T tr => T × tr.type

def Trace.tags : (trace : Trace) → List Name
  | .nil => []
  | .cons n _ tr => n :: tr.tags


@[inline]
def Trace.appendIso {t s : Trace} : (t.append s).type ≃ t.type × s.type :=
  match t, s with
  | .nil, s => {
    toFun := fun x => ((),x)
    invFun := fun (_,x) => x
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  | .cons n T tr, s => {
    toFun := fun (x,y) => let (a,b) := appendIso y; ((x,a),b)
    invFun := fun ((x,x'),y) => (x, appendIso.symm (x',y))
    left_inv := by intro (x,y); simp
    right_inv := by intro ((x,y),z); simp
  }

structure RandWithTrace (X : Type) (trace : Trace) where
  rand : Rand X
  traceRand : Rand trace.type
  map : trace.type → X
  consistent : traceRand.map map = rand

def return' (x : X) : RandWithTrace X .nil where
  rand := Pure.pure x
  traceRand := Pure.pure ()
  map := fun _ => x
  consistent := by simp

def RandWithTrace.bind (x : RandWithTrace X t) (f : X → RandWithTrace Y s)
    (hinter : t.tags.inter s.tags = [] := by simp[Trace.tags,List.inter]; done)
    {tr} (hu : tr = t.append s := by simp[Trace.append,Append.append]; infer_var) : RandWithTrace Y tr where
  rand := x.rand >>= (fun x' => (f x').rand)
  traceRand := do
    let tx ← x.traceRand
    let x := x.map tx
    let ty ← (f x).traceRand
    let t := Trace.appendIso.symm (tx,ty)
    pure (hu ▸ t)
  map s :=
    let (sx,sy) := Trace.appendIso (hu▸s)
    (f (x.map sx)).map sy
  consistent := sorry_proof

def sample {X} (x : Rand X) (tag : Name) :
    RandWithTrace X (.cons tag X .nil) where
  rand := x
  traceRand := do let x ← x; pure (x,())
  map := fun (x,_) => x
  consistent := by simp


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


abbrev RandWithTrace.traceType (x : RandWithTrace X tr) {T} (h : T = tr.type := by simp[Trace.append,Trace.type]; infer_var) := T

def RandWithTrace.map' (x : RandWithTrace X tr) {T} (h : T = tr.type := by simp[Trace.append,Trace.type]; infer_var) := fun t : T => x.map (h▸t)

def RandWithTrace.traceRand' (x : RandWithTrace X tr) {T} (h : T = tr.type := by simp[Trace.append,Trace.type]; infer_var) := do
  let t ← x.traceRand
  return (Eq.mpr h t)

def RandWithTrace.get (x : RandWithTrace X tr) := x.rand.get
def RandWithTrace.getTrace (x : RandWithTrace X tr) {T} (h : T = tr.type := by simp[Trace.append,Trace.type]; infer_var) := (x.traceRand' h).get

def test1 :=
  let x <~ sample (flip 0.5) `v1
  let y <~ sample (normal 0.1 (x.toNat.toFloat)) `v2
  let z <~ sample (uniform (Set.Icc y (2*y))) `v3
  return' (x.toNat.toFloat+y+z)


#eval test1.rand.get
#eval test1.traceRand'.get
#check test1.map'


#eval print_mean_variance test1.rand 1000 ""
#eval print_mean_variance (do let tr ← test1.traceRand; return test1.map tr) 1000 ""
