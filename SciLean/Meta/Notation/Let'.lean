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
    let $x := Prod.fst x
    let $y := Prod.snd x
    $b)
| `(let' ($x,$y) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.snd x
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
