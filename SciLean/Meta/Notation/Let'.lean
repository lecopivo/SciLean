
namespace SciLean

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
syntax (name:=let'_syntax) "let'" "(" ident,* ")" ":=" term ";" term : term

-- TODO: make sure it works for arbitrary number of identitfiers and ideally for arbitrary pattern.
@[inherit_doc let'_syntax]
macro_rules
| `(let' ($x,$y) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.snd x
    $b)
| `(let' ($x,$y,$z) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.snd (Prod.snd x)
    $b)

| `(let' ($x,$y,$z,$w) := $v; $b) =>
  `(let x := $v
    let $x := Prod.fst x
    let $y := Prod.fst (Prod.snd x)
    let $z := Prod.fst (Prod.snd (Prod.snd x))
    let $w := Prod.snd (Prod.snd (Prod.snd x))
    $b)


@[inherit_doc let'_syntax]
macro "let'" "(" "(" x:ident "," y:ident ")" "," z:ident ")" ":=" v:term ";" b:term : term =>
  `(let x := $v
    let $x := x.1.1
    let $y := x.1.2
    let $z := x.2
    $b)
