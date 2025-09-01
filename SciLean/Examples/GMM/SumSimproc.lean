import SciLean

/-! Simproc designed to simplify sums, `∑ i, f i`

Currently it pulls factors that do not depend on the index out of sums i.e.
`∑ i, c * f i` ==> `c * ∑ i, f i`

-/

namespace SciLean.Examples.GMM

open Lean Meta
/-- Take expression full of multiplications and divitions and split it into lists of
  multiplication and division factors.

For example:
```
e = x₁ * x₂         ==> [x₁,x₂] []
e = x₁ * x₂ / y₁    ==> [x₁,x₂] [y₁]
e = x₁ / (y₁/x₂)    ==> [x₁,x₂] [y₁]
e = x₁ * x₂ / y₁ * (x₃ * x₄) / (y₂/x₅)`
                    ==> [x₁,x₂,x₃,x₄,x₄] [y₁,y₂]
```
-/
partial def parse (e : Expr) : Option (List Expr × List Expr × Bool) :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) => do
    match parse e₁, parse e₂ with
    | .none, .none => return ([e₁,e₂], [], false)
    | .some (m₁,d₁,neg₁), .none => return (m₁ ++ [e₂], d₁, neg₁)
    | .none, .some (m₂,d₂,neg₂) => return ([e₁] ++ m₂, d₂, neg₂)
    | .some (m₁,d₁, neg₁), .some (m₂,d₂, neg₂) => return (m₁ ++ m₂, d₁ ++ d₂, neg₁ ^^ neg₂)
  | (``HDiv.hDiv, #[_, _, _, _, e₁, e₂]) =>
    match parse e₁, parse e₂ with
    | none, none => return ([e₁], [e₂], false)
    | .some (m₁,d₁, neg₁), .none => return (m₁, d₁ ++ [e₂], neg₁)
    | .none, .some (m₂,d₂,neg₂) => return (e₁ :: d₂, m₂, neg₂)
    | .some (m₁,d₁,neg₁), .some (m₂,d₂,neg₂) => return (m₁ ++ d₂, d₁ ++ m₂, neg₁ ^^ neg₂)
  | (``Neg.neg, #[_, _, e]) =>
    match parse e with
    | none => return ([e],[],true)
    | some (m,d,neg) => return (m,d,!neg)
  | (``Inv.inv, #[_, _, e]) =>
    match parse e with
    | none => return ([],[e],true)
    | some (m,d,neg) => return (d,m,!neg)
  | _ => return ([e],[],false)


open Qq Lean Meta Mathlib.Tactic in
simproc_decl sum_simproc (sum _) := fun e => do
  let f := e.appArg!
  Lean.Meta.lambdaBoundedTelescope f 1 fun is b => do
    let i := is[0]!

    let .some (m,d,neg) := parse b | return .continue
    let (m₁,m₂) := m.toArray.split (fun e => ¬(e.containsFVar i.fvarId!))
    let (d₁,d₂) := d.toArray.split (fun e => ¬(e.containsFVar i.fvarId!))

    -- skip if all factors depend on the index
    unless m₁.size ≠ 0 ∨ d₁.size ≠ 0 do return .continue

    let X ← inferType b
    let one ← mkAppOptM ``OfNat.ofNat #[X, Expr.lit (.natVal 1), none]

    let merge := fun (m d : Array Expr) => do
      match m.size, d.size with
      | 0, 0 => pure one
      | _, 0 => mkAppFoldlM ``HMul.hMul m
      | 0, _ => mkAppM ``Inv.inv #[← mkAppFoldlM ``HMul.hMul d]
      | _, _ => mkAppM ``HDiv.hDiv #[← mkAppFoldlM ``HMul.hMul m, ← mkAppFoldlM ``HMul.hMul d]

    let mut e₁ ← merge m₁ d₁
    if neg then
       e₁ ← mkAppM ``Neg.neg #[e₁]
    let e₂ ← merge m₂ d₂

    let mut e' ← mkLambdaFVars #[i] e₂
    e' ← mkAppM ``sum #[e']
    e' ← mkAppM ``HMul.hMul #[e₁,e']

    -- if nothing changes there is no need to pulute the proof with sorry
    if e.eqv e' then
       return .continue
    else
      let proof ← mkSorry (← mkEq e e') false
      -- IO.println s!"running simproc on {← ppExpr e}"
      -- IO.println s!"simplified to {← ppExpr e'}"
      -- TODO: here we should have `visit` but it gets into infinite loop :(
      return .done { expr := e', proof? := some proof }
