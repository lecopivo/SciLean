import SciLean.Data.ArrayType.Notation
import SciLean.Data.IndexType.Operations

namespace SciLean

open Lean
open Lean.Elab
open Lean.Elab.Term
open Lean.Meta
open Lean.Parser.Term
open TSyntax.Compat

initialize registerTraceClass `einsum_notation

/--
Einstein summation / `einx`-style notation with named axes.

The core idea is that *axes are identifiers*, not strings. This lets you write expressive
einsum-style programs using descriptive names like `batch`, `channel`, `feature`, ... and Lean
binds them for you.

Syntax:

`einsum[axes₁, axes₂, ... -> outAxes] (x₁, x₂, ...)`

where each `axesᵢ` and `outAxes` is a whitespace-separated list of axis identifiers. Axis
identifiers can optionally be annotated with a type: `(axisName : AxisType)`.

Examples (for `Float^[...]` tensors):

* Matrix multiplication:
  `einsum[row shared, shared col -> row col] (A, B)` expands to
  `⊞ row col => ∑ᴵ shared, A[row,shared] * B[shared,col]`.

* Sum-reduction:
  `einsum[row col -> row] (A)` expands to `⊞ row => ∑ᴵ col, A[row,col]`.

* Transpose / permutation:
  `einsum[row col -> col row] (A)` expands to `⊞ col row => A[row,col]`.

If the `-> outAxes` part is omitted, the output axes default to those appearing *exactly once*
across all inputs (in first-appearance order), matching common `einsum` conventions.

Limitations (for now):
* Output axes must appear in at least one input.
* No ellipsis/broadcasting sugar yet.
-/
declare_syntax_cat einsumAxis

syntax ident : einsumAxis
syntax "(" ident " : " term ")" : einsumAxis

declare_syntax_cat einsumAxes
syntax einsumAxis* : einsumAxes

syntax (name := einsumNotation)
  "einsum" "[" sepBy1(einsumAxes, ",") ("->" einsumAxes)? "]"
    "(" sepBy1(term, ",") ")" : term

private structure AxisOccur where
  name : Name
  ident : TSyntax `ident
  binder : TSyntax `Lean.Parser.Term.funBinder
  annotated : Bool

private def AxisOccur.ppName (a : AxisOccur) : MessageData :=
  m!"{a.ident}"

private def parseAxis (ax : TSyntax `einsumAxis) : TermElabM AxisOccur := do
  match ax with
  | `(einsumAxis| $id:ident) =>
    let b : TSyntax `Lean.Parser.Term.funBinder ← `(funBinder| $id:ident)
    return {
      name := id.getId
      ident := id
      binder := b
      annotated := false
    }
  | `(einsumAxis| ($id:ident : $ty:term)) =>
    let b : TSyntax `Lean.Parser.Term.funBinder ← `(funBinder| ($id:ident : $ty:term))
    return {
      name := id.getId
      ident := id
      binder := b
      annotated := true
    }
  | _ =>
    throwErrorAt ax "einsum axis must be an identifier or `(ident : Type)`, got: {ax}"


private def parseAxes (axs : TSyntax `einsumAxes) : TermElabM (Array AxisOccur) := do
  match axs with
  | `(einsumAxes| $axes:einsumAxis*) =>
    axes.mapM (fun ax => parseAxis ax)
  | _ =>
    throwErrorAt axs "internal error: unexpected einsumAxes syntax {axs}"


private def checkNoDuplicates (ctx : MessageData) (axes : Array AxisOccur) : TermElabM Unit := do
  let mut seen : Std.HashSet Name := {}
  for ax in axes do
    if seen.contains ax.name then
      throwErrorAt ax.ident "duplicate axis {ax.ppName} in {ctx}"
    seen := seen.insert ax.name


private def mkIndexApp (x : TSyntax `term) (idxs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if idxs.isEmpty then
    return x
  else if idxs.size = 1 then
    `(term| $x[$(idxs[0]!)] )
  else
    let i := idxs[0]!
    let is := idxs.extract 1 idxs.size
    `(term| $x[$i, $is,*])


private def mkMulChain (xs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  if xs.isEmpty then
    throwError "einsum: internal error: empty multiplication chain"
  else
    let mut acc := xs[0]!
    for x in xs.extract 1 xs.size do
      acc ← `(term| $acc * $x)
    return acc


private def mkNestedSums (sumAxes : Array AxisOccur) (body : TSyntax `term) : TermElabM (TSyntax `term) := do
  let mut acc := body
  for ax in sumAxes.reverse do
    let b := ax.binder
    acc ← `(term| SciLean.IndexType.sum (fun $b => $acc))
  return acc


private def axisOrderNames (groups : Array (Array AxisOccur)) : Array Name := Id.run do
  let mut order : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  for g in groups do
    for ax in g do
      if !seen.contains ax.name then
        order := order.push ax.name
        seen := seen.insert ax.name
  return order


private def preferAxis (a b : AxisOccur) : AxisOccur :=
  if a.annotated then a else if b.annotated then b else a


private def canonicalAxisMap (groups : Array (Array AxisOccur)) : Std.HashMap Name AxisOccur := Id.run do
  let mut m : Std.HashMap Name AxisOccur := {}
  for g in groups do
    for ax in g do
      match m[ax.name]? with
      | none => m := m.insert ax.name ax
      | some ax' => m := m.insert ax.name (preferAxis ax' ax)
  return m


private def countAxes (groups : Array (Array AxisOccur)) : Std.HashMap Name Nat := Id.run do
  let mut counts : Std.HashMap Name Nat := {}
  for g in groups do
    for ax in g do
      let c := match counts[ax.name]? with
        | some c => c
        | none => 0
      counts := counts.insert ax.name (c + 1)
  return counts


private def computeDefaultOutNames (inGroups : Array (Array AxisOccur)) : Array Name :=
  let order := axisOrderNames inGroups
  let counts := countAxes inGroups
  order.filter fun name =>
    match counts[name]? with
    | some c => c == 1
    | none => false


open Lean Elab Term Meta in
@[term_elab einsumNotation]
def einsumElab : TermElab := fun stx expectedType? => do
  let stxArgs := stx.getArgs
  let openIdx? := stxArgs.findIdx? (fun s => s.isToken "[")
  let closeIdx? := stxArgs.findIdx? (fun s => s.isToken "]")
  let some openIdx := openIdx? | throwErrorAt stx "einsum: malformed syntax: expected `[`"
  let some closeIdx := closeIdx? | throwErrorAt stx "einsum: malformed syntax: expected `]`"
  if openIdx + 1 ≥ closeIdx then
    throwErrorAt stx "einsum: malformed syntax: expected specification between `[` and `]`"

  -- Expected shape (roughly): `einsum` `[` inSpecs outSpec? `]` tensors...
  let inSpecsStx : Array (TSyntax `einsumAxes) :=
    stxArgs[openIdx+1]!.getSepArgs.map (fun s => (⟨s⟩ : TSyntax `einsumAxes))

  let outSpecStx? : Option (TSyntax `einsumAxes) :=
    if openIdx + 2 < closeIdx then
      let outPart := stxArgs[openIdx+2]!
      if outPart.isNone then
        none
      else if outPart.isToken "->" then
        if openIdx + 3 < closeIdx then
          some ⟨stxArgs[openIdx+3]!⟩
        else
          none
      else
        -- `("->" einsumAxes)?` is typically stored as a node containing the pieces.
        -- We try a couple of common shapes to stay robust across parser details.
        match outPart.getArgs with
        | #[outSpec] => some ⟨outSpec⟩
        | #[_, outSpec] => some ⟨outSpec⟩
        | _ =>
          if outPart.getKind == `einsumAxes then
            some ⟨outPart⟩
          else
            none
    else
      none

  let argOpenIdx? := stxArgs.findIdx? (fun s => s.isToken "(")
  let argCloseIdx? := stxArgs.findIdx? (fun s => s.isToken ")")
  let some argOpenIdx := argOpenIdx? | throwErrorAt stx "einsum: malformed syntax: expected `(` after `]`"
  let some argCloseIdx := argCloseIdx? | throwErrorAt stx "einsum: malformed syntax: expected `)`"
  if argOpenIdx + 1 ≥ argCloseIdx then
    throwErrorAt stx "einsum: malformed syntax: expected at least one tensor argument"

  let tensorArgs : Array (TSyntax `term) :=
    stxArgs[argOpenIdx+1]!.getSepArgs.map (fun s => (⟨s⟩ : TSyntax `term))

  let inGroups ← inSpecsStx.mapM parseAxes

  if inGroups.size != tensorArgs.size then
    throwErrorAt stx "einsum: got {tensorArgs.size} tensors but {inGroups.size} axis groups"

  let canon := canonicalAxisMap inGroups
  let orderNames := axisOrderNames inGroups

  let outAxes : Array AxisOccur ←
    match outSpecStx? with
    | some outSpec =>
      let outAxesRaw ← parseAxes outSpec
      checkNoDuplicates (m!"output axes") outAxesRaw
      let mut outAxes : Array AxisOccur := #[]
      for ax in outAxesRaw do
        match canon[ax.name]? with
        | none =>
          throwErrorAt ax.ident "einsum: output axis {ax.ppName} does not occur in any input"
        | some axCanon =>
          outAxes := outAxes.push (if ax.annotated then ax else axCanon)
      pure outAxes
    | none =>
      let outNames := computeDefaultOutNames inGroups
      outNames.mapM fun n =>
        match canon[n]? with
        | some ax => pure ax
        | none => throwError "einsum: internal error: missing canonical axis for {n}"

  let outNameSet : Std.HashSet Name :=
    outAxes.foldl (init := {}) (fun s ax => s.insert ax.name)

  let contractedNames := orderNames.filter (fun n => !outNameSet.contains n)
  let contractedAxes ← contractedNames.mapM fun n =>
    match canon[n]? with
    | some ax => pure ax
    | none => throwError "einsum: internal error: missing canonical axis for {n}"

  -- Build per-operand element access `x[...]`.
  let indexedOperands ← (inGroups.zip tensorArgs).mapM fun (axes, x) => do
    let idxTerms : Array (TSyntax `term) := axes.map (fun ax => (⟨ax.ident.raw⟩ : TSyntax `term))
    mkIndexApp x idxTerms

  let prod ← mkMulChain indexedOperands
  let body ← mkNestedSums contractedAxes prod

  -- If the output has axes, wrap in `⊞ ... =>`; otherwise this is a scalar expression.
  let expanded : TSyntax `term ←
    if outAxes.isEmpty then
      pure body
    else
      let binders : Array (TSyntax `Lean.Parser.Term.funBinder) := outAxes.map (fun ax => ax.binder)
      `(term| ⊞ $binders* => $body)

  trace[einsum_notation] "einsum expands to: {expanded}"
  elabTerm expanded expectedType?

end SciLean
