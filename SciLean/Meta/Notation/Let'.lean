import Lean
namespace SciLean

open Lean Parser.Term
/-- Variant of let binding for product pattern that does not desugar into match but into
bunch of other let bindings and projections.

For examples
```
let' (x,y) := v;
b
```
expands into
```
let p := v
let x := p.1
let y := p.2
b
```
-/

syntax (name:=let'_syntax) withPosition("let'" "(" ident,* ")" ":=" term) optSemicolon(term) : term


-- TODO: make sure it works for arbitrary number of identitfiers and ideally for arbitrary pattern.
@[inherit_doc let'_syntax]
macro_rules (kind :=let'_syntax)
| `(let' ($x,$y) := $v
    $b) =>
  `(let x := $v
    let $x := x.1
    let $y := x.2
    $b)
| `(let' ($x,$y) := $v; $b) =>
  `(let x := $v
    let $x := x.1
    let $y := x.2
    $b)

| `(let' ($x,$y,$z) := $v
    $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.snd (Prod.snd x)
    $b)
| `(let' ($x,$y,$z) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.snd (Prod.snd x)
    $b)


| `(let' ($x,$y,$z,$w) := $v
    $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.fst (Prod.snd (Prod.snd x))
    let $w := Prod.snd (Prod.snd (Prod.snd x))
    $b)
| `(let' ($x,$y,$z,$w) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.fst (Prod.snd (Prod.snd x))
    let $w := Prod.snd (Prod.snd (Prod.snd x))
    $b)

| `(let' ($x,$y,$z,$w,$a) := $v
    $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.fst (Prod.snd (Prod.snd x))
    let $w := Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))
    let $a := Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))
    $b)
| `(let' ($x,$y,$z,$w,$a) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.fst (Prod.snd (Prod.snd x))
    let $w := Prod.fst (Prod.snd (Prod.snd (Prod.snd x)))
    let $a := Prod.snd (Prod.snd (Prod.snd (Prod.snd x)))
    $b)


syntax (name:=let'_syntax') withPosition("let'" "(" "(" ident "," ident ")" "," ident ")" ":=" term) optSemicolon(term) : term

@[inherit_doc let'_syntax]
macro_rules (kind :=let'_syntax')
| `(let' (($x,$y),$z) := $v
    $b) =>
  `(let x := $v
    let $x := x.1.1
    let $y := x.1.2
    let $z := x.2
    $b)
| `(let' (($x,$y),$z) := $v; $b) =>
  `(let x := $v
    let $x := x.1.1
    let $y := x.1.2
    let $z := x.2
    $b)

syntax (name:=let'_syntax'') withPosition("let'" "(" "(" ident "," ident ")" "," "(" ident "," ident ")"  ")" ":=" term) optSemicolon(term) : term

@[inherit_doc let'_syntax]
macro_rules (kind :=let'_syntax'')
| `(let' (($x,$y),($z,$w)) := $v
    $b) =>
  `(let x := $v
    let $x := x.1.1
    let $y := x.1.2
    let $z := x.2.1
    let $w := x.2.2
    $b)
| `(let' (($x,$y),($z,$w)) := $v; $b) =>
  `(let x := $v
    let $x := x.1.1
    let $y := x.1.2
    let $z := x.2.1
    let $w := x.2.2
    $b)


/-- Let binding that deconstructs structure into its fields.

The notation
```
let ⟨..⟩ := s
b
```
expands to
```
let ⟨x₁,...,xₙ⟩ := s
b
```
where `x₁` are field names of struct `s`.

For example, `Prod` has field `fst` and `snd` therefore
```
let ⟨..⟩ := (1,2)
fst + snd
```
as it expands to
```
let ⟨fst,snd⟩ := (1,2)
fst + snd
```
 -/
syntax (name:=let_struct_syntax) withPosition("let" "⟨..⟩" ":=" term) optSemicolon(term) : term

open Lean Elab Term Syntax Meta
elab_rules (kind:=let_struct_syntax) : term
| `(let ⟨..⟩ := $x:term
    $b) => do

  let X ← inferType (← elabTerm x none)
  let .const struct _ := X.getAppFn' | throwError "structure expected"
  let info := getStructureInfo (← getEnv) struct
  let ids := info.fieldNames.map (fun n => mkIdent n)
  let stx ← `(let ⟨$ids,*⟩ := $x; $b)
  elabTerm stx none


/-- Structure field assigment, allows for `s.x := x'` notation in `do` block.

`s.x := x'` expands into `s := {s with x := x'}` -/
macro_rules
| `(doElem| $x:ident := $val) => do
  let .str n f := x.getId | Macro.throwUnsupported
  if n == .anonymous then Macro.throwUnsupported
  let o := mkIdentFrom x n
  let field := mkIdentFrom x (Name.mkSimple f)
  `(doElem| $o:ident := {$o with $field:ident := $val})
