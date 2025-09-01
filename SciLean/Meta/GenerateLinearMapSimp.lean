import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.LinearMap.Defs

import SciLean.Data.IndexType
import SciLean.Meta.SimpAttr

import SciLean.Tactic.AnalyzeConstLambda

namespace SciLean

set_option linter.unusedVariables false

section HelperTheorems

universe u'

set_option deprecated.oldSectionVars true

variable
  {K : Type u'} [CommSemiring K]
  {X : Type u} [AddCommGroup X] [Module K X]
  {Y : Type v} [AddCommGroup Y] [Module K Y]
  {Z : Type w} [AddCommGroup Z] [Module K Z]
  {f : X → Y} (hf : IsLinearMap K f)

theorem _root_.IsLinearMap.add_push (x x' : X)
  : f x + f x' = f (x + x') := by rw[hf.map_add]

theorem _root_.IsLinearMap.add_pull (x x' : X)
  : f (x + x') = f x + f x' := by rw[hf.map_add]

-- todo: this is not sufficiently universe polymorphic
--       and somethimes forces to write non-universe polymorphic code
--       fix this
-- theorem _root_.IsLinearMap.sum_push
--   (ι : Type) [IndexType ι] (x : ι → X)
--   : (∑ i : ι, f (x i)) = f (∑ i, x i) := by sorry_proof

-- todo: this is not sufficiently universe polymorphic
--       and somethimes forces to write non-universe polymorphic code
--       fix this
-- theorem _root_.IsLinearMap.sum_pull
--   {f : X → Y} (hf : IsLinearMap K f)
--   (ι : Type) [IndexType ι] (x : ι → X)
--   : f (∑ i, x i) = ∑ i, f (x i) := by sorry_proof

theorem _root_.IsLinearMap.sub_push (x x' : X)
  : f x - f x' = f (x - x') := by rw[hf.map_sub]

theorem _root_.IsLinearMap.sub_pull (x x' : X)
  : f (x - x') = f x - f x' := by rw[hf.map_sub]

theorem _root_.IsLinearMap.smul_push (x : X) (k : K)
  : k • f x = f (k • x) := by rw[hf.map_smul]

theorem _root_.IsLinearMap.smul_pull (x : X) (k : K)
  : f (k • x) = k • f x := by rw[hf.map_smul]

theorem _root_.IsLinearMap.neg_push (x : X)
  : - f x = f (- x) := by rw[hf.map_neg]

theorem _root_.IsLinearMap.neg_pull (x : X)
  : f (- x) = - f x := by rw[hf.map_neg]

theorem _root_.IsLinearMap.app_zero
  : f 0 = 0 := by rw[hf.map_zero]

variable {g : X → Y → Z} (hg : IsLinearMap K fun xy : X×Y => g xy.1 xy.2)

theorem _root_.IsLinearMap.add_push₂ (x x' : X) (y y' : Y)
  : g x y + g x' y' = g (x + x') (y + y') :=
by
  have h := hg.map_add (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsLinearMap.add_pull₂  (x x' : X) (y y' : Y)
  : g (x + x') (y + y') = g x y + g x' y' :=
by
  have h := hg.map_add (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsLinearMap.sub_push₂ (x x' : X) (y y' : Y)
  : g x y - g x' y' = g (x - x') (y - y') :=
by
  have h := hg.map_sub (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsLinearMap.sub_pull₂  (x x' : X) (y y' : Y)
  : g (x - x') (y - y') = g x y - g x' y' :=
by
  have h := hg.map_sub (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsLinearMap.smul_push₂ (x : X) (y : Y) (k : K)
  : k • g x y = g (k • x) (k • y) :=
by
  have h := hg.map_smul k (x,y)
  simp at h; rw[h]

theorem _root_.IsLinearMap.smul_pull₂ (x : X) (y : Y) (k : K)
  : g (k • x) (k • y) = k • g x y  :=
by
  have h := hg.map_smul k (x,y)
  simp at h; rw[h]

theorem _root_.IsLinearMap.neg_push₂ (x : X) (y : Y)
  : - g x y = g (- x) (- y) :=
by
  have h := hg.map_neg (x,y)
  simp at h; rw[h]

theorem _root_.IsLinearMap.neg_pull₂ (x : X) (y : Y)
  : g (- x) (- y) = - g x y :=
by
  have h := hg.map_neg (x,y)
  simp at h; rw[h]

theorem _root_.IsLinearMap.app_zero₂
  : g 0 0 = 0 :=
by
  have h := hg.map_zero
  simp at h; rw[h]


end HelperTheorems


open Lean Meta
def generateLinearMapSimp
  (ctx : Array Expr) (isLinearMap : Expr)
  (thrmName : Name) (isSimpAttr : Bool := true) (makeSimp : Bool := false) : MetaM Unit := do

  let f := (← inferType isLinearMap).getArg! 8
  let data ← analyzeConstLambda f

  if data.mainArgs.size > 2 then
    throwError s!"generating simp theorems for linear functions in {data.mainArgs.size} arguments is not supported"

  let mut fullThrmName := (``IsLinearMap).append thrmName
  if data.mainArgs.size = 2 then
    fullThrmName := fullThrmName.appendAfter "₂"

  let proof ← mkAppM fullThrmName #[isLinearMap]
  let proof ← mkLambdaFVars ctx proof
  let statement ← inferType proof

  let simpThrmName := data.constName |>.append (.mkSimple data.declSuffix) |>.append thrmName
  let thrmVal : TheoremVal :=
  {
    name  := simpThrmName
    type  := statement
    value := proof
    levelParams := (collectLevelParams {} statement).params.toList
  }

  -- don't add theorem if it already exists
  if ((← getEnv).find? simpThrmName).isSome then
    return ()

  addDecl (.thmDecl thrmVal)

  if isSimpAttr then
    let .some ext := (← simpExtensionMapRef.get)[thrmName]?
      | throwError s!"{thrmName} is not a simp attribute"
    addSimpTheorem ext thrmVal.name false false .global (eval_prio default)

  if makeSimp then
    let .some ext := (← simpExtensionMapRef.get)[`simp]?
      | throwError s!"simp is not a simp attribute"
    addSimpTheorem ext thrmVal.name false false .global (eval_prio default)

    let .some ext := (← simpExtensionMapRef.get)[`simp_core]?
      | throwError s!"simp_core is not a simp attribute"
    addSimpTheorem ext thrmVal.name false false .global (eval_prio default)


open Lean Meta
/-- Generates bunch of simp theorems given a proof that function is linear.

The provided theorem should be in the simple form `IsLinearMap K (fun x => foo x)`
Not in the composition form `IsLinearMap K (fun x => foo (f x))`
-/
def generateLinearMapSimps (isLinearMapTheorem : Name) : MetaM Unit := do

  let info ← getConstInfo isLinearMapTheorem

  lambdaTelescope info.value! fun ctx isLinearMap => do

    let pullpush := [`add_pull,`add_push, `sub_pull,`sub_push,`smul_pull,`smul_push,`neg_pull,`neg_push]

    for thrm in pullpush do
      generateLinearMapSimp ctx isLinearMap thrm

    let simps := [`app_zero]

    for thrm in simps do
      generateLinearMapSimp ctx isLinearMap thrm (isSimpAttr:=false) (makeSimp:=true)


/-- This commands generates simp lemmas for given linear function.

The commands is used as
```
#generate_linear_map_simps thrmName
```
where `thrmName` is a name of a theorem that states that function `f` is linear i.e. `IsLinearMap K f`.

The command generates theorems
```
@[add_push] theorem add_push (x x' : X) : f x + f x' = f (x + x') := ...
@[add_pull] theorem add_pull (x x' : X) : f (x + x') = f x + f x' := ...
@[sub_push] theorem sub_push (x x' : X) : f x - f x' = f (x - x') := ...
@[sub_pull] theorem sub_pull (x x' : X) : f (x - x') = f x - f x' := ...
@[neg_push] theorem neg_push (x : X)    : - f x = f (- x) := ...
@[neg_pull] theorem neg_pull (x : X)    : f (- x) = - f x := ...
@[smul_push] theorem smul_push (x : X) (k : K) : k • f x = f (k • x) := ...
@[smul_pull] theorem smul_pull (x : X) (k : K) : f (k • x) = k • f x := ...
@[simp] theorem app_zero : f 0 = 0 := ...
```
All the above attributes are simp attributes. The ideas is that you can propagate
arithmetic operations by calling `simp` e.g. `simp only [add_pull]`.


The command also supports functions jointly linear in two arguments. If we have
`g : X → Y → Z` and `g_is_linear₂ : IsLinear K fun (x,y) => g x y` then
```
#generate_linear_map_simps g_is_linear₂
```
generates theorems like
```
@[add_push] theorem add_push (x x' : X) (y y' : Y) : g x y + g x' y' = g (x + x') (y + y') := ...
...
```

-/
syntax (name:=genLinMapSimpsNotation) "#generate_linear_map_simps " ident : command

open Lean Elab Term Command
elab_rules : command
| `(#generate_linear_map_simps $thrm) => do
  let thmName ← resolveGlobalConstNoOverload thrm
  liftTermElabM <| generateLinearMapSimps thmName
