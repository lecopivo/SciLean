import Lean
import Mathlib.Logic.Nonempty
import SciLean.Lean.Meta.Basic
import SciLean.Lean.Array
import SciLean.Data.Curry
import SciLean.Tactic.LetEnter
import SciLean.Tactic.LetNormalize

namespace SciLean

attribute [local instance] Classical.propDecidable

def HasUniqueSolution {F Xs} [UncurryAll F Xs Prop] (P : F) :=
  (∃ xs, uncurryAll P xs)
  ∧
  ∀ xs xs', uncurryAll P xs → uncurryAll P xs' → xs = xs'

noncomputable
def solveFun {F : Sort _} {Xs : outParam (Type _)} [UncurryAll F Xs Prop] [Nonempty Xs] (f : F) : Xs :=
  if h : HasUniqueSolution f then
    Classical.choose h.1
  else
    Classical.arbitrary Xs


open Lean Parser Elab Term in
elab "solve" xs:funBinder* ", " b:term : term => do
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
  := by sorry



/-- This theorem allows us to decompose one problem into two succesives problems
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
  := by sorry

namespace SolveFun


open Lean Meta

/-- Take and expresion of the form `P₁ ∧ ... ∧ Pₙ` and return array `#[P₁, ..., Pₙ]` -/
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
  IO.println s!"e:\n{← ppExpr e}\n"
  if e.isAppOfArity ``solveFun 5 then
    lambdaTelescope (e.getArg! 4) fun xs b => do
      let is := is.sortAndDeduplicate
      let js := js.sortAndDeduplicate
      let Ps ← splitAnd? b

      if ¬(is.all (·<xs.size) ∧ js.all (·<Ps.size)) then
        throwError "Error in solveForFrom: invalid index when looking for variable {is} and equations {js} in\n{← ppExpr e}"

      let (ys,zs,ids) := xs.splitIdx (fun i _ => ¬(is.contains i.1))
      let (Qs₁,Qs₂,_) := Ps.splitIdx (fun j _ => js.contains j.1)
     
      let zsName ← zs.joinlM (fun z => z.fvarId!.getUserName) (fun a b => pure <| a.appendAfter b.toString)
      let ysName ← ys.joinlM (fun y => y.fvarId!.getUserName) (fun a b => pure <| a.appendAfter b.toString)

      let Q₁body ← mkAppFoldrM ``And Qs₁
      let Q₁ ← mkLambdaFVars zs Q₁body

      let zs'Val ← mkLambdaFVars ys (← mkAppM ``solveFun #[Q₁])
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
      let eqProof ← mkAppM ``sorryAx #[← mkEq e e', .const ``Bool.false []]

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
syntax (name:=solve_for) "solve_for " ident+ " from " num+ " := " term : conv 


open Lean Elab Tactic Conv
@[tactic solve_for] def solveForTactic : Tactic := fun stx => 
  withMainContext do
  match stx with
  | `(conv| solve_for $xs* from $js* := $prf) => do
    let names := xs.map (fun x => x.getId)
    let js := js.map (fun j => j.getNat)
    let lhs ← getLhs
    
    let (lhs', eq, uniqueMVar) ← withMainContext <| solveForNameFrom lhs names js

    let uniqueProof ← elabTerm prf (← uniqueMVar.getType)
    uniqueMVar.assign uniqueProof

    updateLhs lhs' eq

  | _ => throwUnsupportedSyntax


-- example : (0,0,0) = (solve (a b c : Nat), a+b+c=1 ∧ a-b+c=1 ∧ a-b-c=1) := 
-- by
--   conv =>
--     rhs
--     solve_for b from 2 := sorry
--     conv => 
--       enter_let ac
--       solve_for a from 0 := sorry
--     let_normalize
