import SciLean.Tactic.InferVar
import SciLean.Util.RewriteBy

import SciLean.Probability.Rand
import SciLean.Probability.Distributions.Flip
import SciLean.Probability.Distributions.Normal
import SciLean.Probability.Distributions.Uniform

import SciLean.Analysis.Scalar.FloatAsReal

open Lean

set_option linter.unusedVariables false

namespace SciLean.Rand

inductive Trace where
| nil
| single (tag : Name) (T : Type)
| pair (t s : Trace)
| array (t : Trace) (n : Nat)

instance : Append Trace := ⟨fun t s => .pair t s⟩

def Trace.type : (trace : Trace) → Type
  | .nil => Unit
  | .single n T => T
  | .pair t s => t.type × s.type
  | .array t n => Vector t.type n -- {a : Array t.type // a.size = n}

def Trace.tags : (trace : Trace) → List Name
  | .nil => []
  | .single n _ => [n]
  | .pair t s => t.tags ++ s.tags
  | .array t n =>
    let ts := t.tags.map (fun tag => (List.range n).map (fun i => tag.append (.mkSimple (toString i))))
    ts.foldl (init:=[]) (·++·)

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

macro "trace_bind_tac" : tactic =>
  `(tactic| first | native_decide
                  | simp only [Trace.tags,
                       List.inter,
                       List.elem_eq_mem,
                       List.find?_nil,
                       List.filter_cons_of_neg,
                       List.filter_nil,
                       Bool.false_eq_true,
                       not_false_eq_true
                       decide_False] )



def RandWithTrace.bind (x : RandWithTrace X t T) (f : X → RandWithTrace Y s S)
    (hinter : t.tags.inter s.tags = [] := by trace_bind_tac) :
    RandWithTrace Y (t++s) (T×S) where
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
    -- rw[← (f sorry).htype]
    sorry_proof

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
  try runTactic e.mvarId! (← `(term| by unfold autoParam; ($stx:tacticSeq))) .term false
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


-- #eval test2.rand.get
-- #eval test2.traceRand.get
-- #eval do pure (test2.map (← test2.traceRand.get))


variable {R} [RealScalar R]
open MeasureTheory


def forLoop (f : Nat → X → RandWithTrace X t T) (init : X) (n : Nat) :
    RandWithTrace X (.array t n) (Vector T n) where
  rand := do
    let mut x := init
    for i in [0:n] do
      x ← (f i x).rand
    return x
  traceRand := do
    let mut ws : Array T := #[]
    let mut x := init
    for i in [0:n] do
      let w ← (f i x).traceRand
      ws := ws.push w
      x := (f i x).map w
    return ⟨ws, sorry_proof⟩
  map := fun ws => Id.run do
    let mut x := init
    for w in ws.1, i in [0:n] do
      x := (f i x).map w
    return x
  hmap := sorry_proof
  htype := by sorry_proof

@[simp]
theorem trace_bind_pdf (x : RandWithTrace X t T) (f : X → RandWithTrace Y s S)
  (h : t.tags.inter s.tags = [] := by trace_bind_tac)
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



-- structure HasConditionalRand {X tr T} (x : RandWithTrace X tr T) (tags : List Name)
--     (tr₁ tr₂ : Trace) (T₁ T₂ : Type)
--     (p : T → T₁×T₂) (q : T₁ → T₂ → T)
--     (y : RandWithTrace T₁ tr₁ T₁) (z : T₁ → RandWithTrace X tr₂ T₂) : Prop where
--   trace_type₁ : tr₁.type = T₁
--   trace_type₂ : tr₂.type = T₂
--   left_inv : Function.LeftInverse p ↿q
--   right_inv : Function.RightInverse p ↿q
--   trace_tags  : tr₁.tags = tags
--   trace_union : tr₁ ++ tr₂ = tr
--   trace_inter : tr₁.tags.inter tr₂.tags = []
--   hrand : x.traceRand = (do
--     let ty ← y.traceRand;
--     let tz ← (z ty).traceRand
--     return q ty tz)
--   hmap : x.map = fun w =>
--     let (u,v) := u
--     (z (y.map u)).map v


-- theorem HasConditionalRand.empty_rule (x : RandWithTrace X tr T) :
--    HasConditionalRand x []
--      .nil tr Unit T (fun t => ((),t)) (fun _ t => t)
--      (return' ()) (fun _ => x) := sorry_proof


-- theorem HasConditionalRand.bind_rule
--    (x : RandWithTrace X t T) (f : X → RandWithTrace Y s S) (tags : List Name)
--    (hinter : t.tags.inter s.tags = [])
--    (hx : HasConditionalRand x (t.tags.inter tags) t₁ t₂ T₁ T₂ px qx x₁ x₂)
--    {y₁ : X → RandWithTrace Unit s₁ S₁} {y₂ : X → S₁ → RandWithTrace Y s₂ S₂}
--    (hy : ∀ x, HasConditionalRand (f x) (s.tags.inter tags) s₁ s₂ S₁ S₂ py qy (y₁ x) (y₂ x)) :
--    HasConditionalRand (x.bind f hinterx) tags
--      (t₁++s₁) (t₂++s₂) (T₁×S₁) (T₂×S₂)
--      (fun (u,v) => (((px u).1, (py v).1),((px u).2, (py v).2)))
--      (fun (u₁,v₁) (u₂,v₂) => (qx u₁ u₂, qy v₁ v₂))
--      (x₁.bind (fun tx => y₁ (x₁.map tx)) sorry)
--      sorry := sorry_proof
