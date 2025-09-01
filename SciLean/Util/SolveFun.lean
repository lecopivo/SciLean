import Lean
import Mathlib.Logic.Nonempty
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.Group.Int.Defs

import SciLean.Data.Curry
import SciLean.Lean.Meta.Basic
import SciLean.Lean.Array
import SciLean.Tactic.LetNormalize
import SciLean.Util.SorryProof

import Batteries.Data.Array.Merge

namespace SciLean

set_option linter.unusedVariables false

open Classical

-- TODO: ditch `UncurryAll` and use mathlib's `Function.Uncurry`

structure HasSolution {F Xs} [UncurryAll F Xs Prop] (P : F) : Prop where
  ex : ∃ xs, uncurryAll P xs

structure HasUniqueSolution {F Xs} [UncurryAll F Xs Prop] (P : F) : Prop extends HasSolution P where
  uniq : ∀ xs xs', uncurryAll P xs → uncurryAll P xs' → xs = xs'

/-- Finds unique `(x₁, ..., xₙ)` such that `P x₁ ... xₙ` holds.

TODO: Can we return a solution if it exists and it not necessarily unique? I'm not sure if we would be able to prove `decomposeSolution` then.

TODO: This is related to mathlib's `Classical.epsilon` i.e. the Hilbert epsilon function. Maybe redefine this function using it.
-/
noncomputable
def solveFun {F : Sort _} {Xs : outParam (Type _)} [UncurryAll F Xs Prop] [Nonempty Xs] (f : F /- Xs → ... → Prop -/) : Xs :=
  if h : HasUniqueSolution f then
    Classical.choose h.ex
  else
    Classical.arbitrary Xs


open Lean Parser Elab Term in
/-- Expresses the unique solution of a system of equations if it exists

For example

```
solve x y, x + y = a ∧ x - y = b
```
returns a pair `(x,y)` that solve the above system

The returned value is not specified if the system does not have an unique solution.
-/
elab (priority:=high) "solve" xs:funBinder* ", " b:term : term => do
  let stx ← `(fun $xs* => $b)
  let f ← elabTerm stx.raw none
  Meta.mkAppM ``solveFun #[f]


@[app_unexpander solveFun] def unexpandSolveFun : Lean.PrettyPrinter.Unexpander

  | `($(_) fun $xs* => $b) =>
    `(solve $xs*, $b)
  | _  => throw ()


-- I'm fairly confident that this is true
-- this should quarantee us that the decomposition is sound
theorem decompose_has_unique_solution {Xs Ys Zs : Type _} [Nonempty Xs] [Nonempty Ys] [Nonempty Zs]
  (f : Ys → Zs → Xs)  -- decomposition of unknowns
  (hf : Function.Bijective (uncurryN 2 f))     -- together with `unique₁` and `unique₂` we can show `HasUniqueSolution f`
  (P : Xs → Prop)       -- original problem
  (Q₁ : Ys → Zs → Prop) (Q₂ : Ys → Zs → Prop) -- decomposition into two problems
  (equiv : ∀ ys zs, (Q₁ ys zs ∧ Q₂ ys zs) ↔ P (f ys zs))
  (unique : ∀ ys, HasUniqueSolution (Q₁ ys))
  : HasUniqueSolution P
    ↔
    HasUniqueSolution fun ys => Q₂ ys (solve zs, Q₁ ys zs)
  := by sorry_proof



/-- This theorem allows us to decompose one problem `P` into two succesives problems `Q₁` and `Q₂`.
-/
theorem decomposeSolution {Xs Ys Zs : Type _} [Nonempty Xs] [Nonempty Ys] [Nonempty Zs]
  (f : Ys → Zs → Xs)  -- decomposition of unknowns
  (hf : Function.Bijective (uncurryN 2 f))     -- together with `unique₁` and `unique₂` we can show `HasUniqueSolution f`
  (P : Xs → Prop)       -- original problem
  (Q₁ : Ys → Zs → Prop) (Q₂ : Ys → Zs → Prop) -- decomposition into two problems
  (equiv : ∀ ys zs, (Q₁ ys zs ∧ Q₂ ys zs) ↔ P (f ys zs))
  (unique : ∀ ys, HasUniqueSolution (Q₁ ys))
  : (solve xs, P xs)
    =
    let zs' := fun ys => (solve zs, Q₁ ys zs)
    let ys  := solve ys, Q₂ ys (zs' ys)
    let zs  := zs' ys
    f ys zs
  := by sorry_proof

namespace SolveFun


open Lean Meta

/-- Take and expresion of the form `P₁ ∧ ... ∧ Pₙ` and return array `#[P₁, ..., Pₙ]`

It ignores bracketing, so both `(P₁ ∧ P₂) ∧ P₃` and `P₁ ∧ (P₂ ∧ P₃)` produce `#[P₁, P₂, P₃]`-/
def splitAnd? (e : Expr) : MetaM (Array Expr) := do
  match e with
  | .mdata _ e' => splitAnd? e'
  | .app (.app (.const name _) x) y =>
    if name ≠ ``And then
      return #[e]
    else
      let l1 ← splitAnd? x
      let l2 ← splitAnd? y
      return (l1.append l2)
  | e => return #[e]


/-- Decompose `solve` problem into two `solve` problems. First, solve specified equations with indices `js` w.r.t to unknowns with indices `is`. Afterward, solve remaining equations w.r.t. remaining unknowns.

Returns:

1. the decomposed problem

2. proof that it is equivalent to the original problem

3. proof obligation that the decomposed problem has unique solution

---

For example calling `solveForFrom · #[1,3] #[0,1]` on

```
  solve x y z w, P ∧ Q ∧ R ∧ T
```

will return

```
  let yw' := fun x z => solve y w, P ∧ Q

  fun (x,z) := solve x z, R ∧ T

  let (y,w) := yw' x z

  (x,y,z,w)
```

TODO: This should produce proof that those two terms are equal
-/
def solveForFrom (e : Expr) (is js : Array Nat) : MetaM (Expr×Expr×MVarId) := do
  if e.isAppOfArity ``solveFun 5 then
    lambdaTelescope (e.getArg! 4) fun xs b => do
      let is := is.sortDedup
      let js := js.sortDedup
      let Ps ← splitAnd? b

      if let .some i := is.find? (· ≥ xs.size) then
        throwError "cant' decompose `solve` with respect to the unknown `{i}` as there are only {xs.size} unknowns"

      if let .some j := js.find? (· ≥ Ps.size) then
        throwError "cant' decompose `solve` with respect to the equation `{j}` as there are only {Ps.size} equations"

      if ¬(is.size < xs.size) then
        throwError "can't decompose `solve` with respect to all unknowns"

      if ¬(js.size < Ps.size) then
        throwError "can't decompose `solve` with respect to all equations"

      let (ys,zs,ids) := xs.splitIdx (fun i _ => ¬(is.contains i.1))
      let (Qs₁,Qs₂,_) := Ps.splitIdx (fun j _ => js.contains j.1)

      let zsName ← zs.joinlM (fun z => z.fvarId!.getUserName) (fun a b => pure <| a.appendAfter b.toString)
      let ysName ← ys.joinlM (fun y => y.fvarId!.getUserName) (fun a b => pure <| a.appendAfter b.toString)

      let Q₁body ← mkAppFoldrM ``And Qs₁
      let Q₁ ← mkLambdaFVars zs Q₁body

      let zs'Val ← mkAppM ``solveFun #[Q₁] >>= mkLambdaFVars ys  -- >>= (mkAppM ``hold #[·]) -- (← mkAppM ``solveFun #[Q₁])
      withLetDecl (zsName.appendAfter "'") (← inferType zs'Val) zs'Val fun zs'Var => do

      let zs' ← mkProdSplitElem (← mkAppM' zs'Var ys) zs.size

      let mut Q₂body ← mkAppFoldrM ``And Qs₂
      for z in zs, z' in zs' do
        Q₂body := Q₂body.replaceFVar z z'

      let Q₂ ← mkLambdaFVars ys Q₂body

      let ysVal ← mkAppM ``solveFun #[Q₂]
      withLetDecl ysName (← inferType ysVal) ysVal fun ysVar => do

      let zsVal ← mkAppM' zs'Var (← mkProdSplitElem ysVar ys.size)
      withLetDecl zsName (← inferType zsVal) zsVal fun zsVar => do

      let xs ← ids.mapM (fun id : Sum Nat Nat =>
        match id with
        | .inl i => mkProdProj ysVar i ys.size
        | .inr i => mkProdProj zsVar i zs.size)
      >>= mkProdElem

      let e' ← mkLambdaFVars #[zs'Var, ysVar, zsVar] xs


      let unique ← mkForallFVars ys (← mkAppM ``HasUniqueSolution #[Q₁])
      let uniqueProof ← mkFreshExprMVar unique

      -- somehow we should be able to combine everyting with the theorem `decomposeSolution` to obtain equality proof
      let eqProof ← mkAppOptM ``sorryProofAxiom #[← mkEq e e']

      -- if ¬(← isTypeCorrect eqProof) then
      --   throwError "something went wrong :("

      return (e',eqProof, uniqueProof.mvarId!)
  else do
    throwError "Error in solveForFrom: not application of `solveFun`\n{← ppExpr e}"


def solveForNameFrom (e : Expr) (names : Array Name) (js : Array Nat) : MetaM (Expr×Expr×MVarId) := do
  if e.isAppOfArity ``solveFun 5 then do
    let is ← lambdaTelescope (e.getArg! 4) fun xs _ =>
      names.mapM (fun name => do
        let .some i ← xs.findIdxM? (fun x => do pure <| (← x.fvarId!.getUserName) = name)
          | throwError "no unknown with the name `{name}`"
        pure i)
    solveForFrom e is js
  else
    throwError "not an expression of the form `solve x₁ .. xₙ, P₁ ∧ ... ∧ Pₘ`"




open Lean Parser Syntax

/--
Tactic `solve_for y w from 0 1 := uniq` will decompose `solve x y z w, ...` problem
by first solving for `y` and `w` from `0`th and `2`th equations and then solving the rest.
You have to provide proof `uniq` that the decomposed problem has unique solution.

---

For example, calling `solve_for y w from 0 1 := by ...` on:

```
  solve x y z w, P ∧ Q ∧ R ∧ T
```

produces

```
  let yw' := fun x z => solve y w, P ∧ Q

  fun (x,z) := solve x z, R ∧ T

  let (y,w) := yw' x z

  (x,y,z,w)
```

Warring: this tactic currently uses `sorry`!-/
local syntax (name:=solve_for_core_tactic) "solve_for_core " ident+ " from " num+ " := " term : conv

@[inherit_doc solve_for_core_tactic]
macro (name:=solve_for_tacitc) "solve_for " xs:ident+ " from " js:num+ " := " uniq:term : conv =>
  `(conv| ((conv => pattern (solveFun _); solve_for_core $xs* from $js* := $uniq); let_normalize (config := {removeLambdaLet:=false})))


open Lean Elab Tactic Conv
@[tactic solve_for_core_tactic] def solveForTactic : Tactic := fun stx =>
  withMainContext do
  match stx with
  | `(conv| solve_for_core $xs* from $js* := $prf) => do
    let names := xs.map (fun x => x.getId)
    let js := js.map (fun j => j.getNat)
    let lhs ← getLhs

    let (lhs', eq, uniqueMVar) ← withMainContext <| solveForNameFrom lhs names js

    let uniqueProof ← elabTerm prf (← uniqueMVar.getType)
    uniqueMVar.assign uniqueProof

    updateLhs lhs' eq

  | _ => throwUnsupportedSyntax


open Function
/--
Rewrite `solve` as `invFun`

TODO: There might be slight inconsistency as `invFun` always tries to give you some kind of answer even if it is not uniquely determined but `solve` gives up if the answer is not unique.

The issue is that I'm not sure if
`Classical.choose (∃ x, f x - g x = 0)` might not be the same as `Classical.choose (∃ x, f x = g x)` or is that
-/
theorem solve_as_invFun {α β : Type _} [Nonempty α] (f g : α → β) [AddGroup β]
  : (solve x, f x = g x)
    =
    invFun (fun x => f x - g x) 0
  := sorry_proof


theorem solve_as_invFun_lhs {α β : Type _} [Nonempty α] (f : α → β) (b : β) [AddGroup β]
  : (solve x, f x = b)
    =
    invFun f b
  := sorry_proof

theorem solve_as_invFun_rhs {α β : Type _} [Nonempty α] (f : α → β) (b : β) [AddGroup β]
  : (solve x, b = f x)
    =
    invFun f b
  := sorry_proof


macro "solve_as_inv" : conv => `(conv| (conv => pattern (solveFun _); first | rw[solve_as_invFun_lhs] | rw[solve_as_invFun_rhs] | rw[solve_as_invFun]))



/--
info: let b' := fun a c => invFun (fun b => a - b - c) 1;
let a' := fun c => invFun (fun a => a + b' a c + c) 1;
let c := invFun (fun c => a' c - b' (a' c) c + c) 1;
let a := a' c;
let b := b' a c;
(a, b, c) : ℤ × ℤ × ℤ
-/
#guard_msgs in
#check
  (solve (a b c : Int), a+b+c=1 ∧ a-b+c=1 ∧ a-b-c=1)
  rewrite_by
    solve_for b from 2 := sorry_proof
    solve_as_inv
    solve_for a from 0 := sorry_proof
    solve_as_inv
    solve_as_inv

/--
info: let a' := fun b => solve a, ∀ (c : ℕ), a + c = c;
let b := solve b, ∀ (c : ℕ), a' b + b + c = c;
let a := a' b;
(a, b) : ℕ × ℕ
-/
#guard_msgs in
#check
  (solve (a b : Nat), (∀ c, a + b + c = c) ∧ (∀ c, a + c = c))
  rewrite_by
    solve_for a from 1 := sorry_proof
