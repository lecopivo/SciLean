module

public import Mathlib.Algebra.Module.Basic

public meta import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Prod
public meta import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.LinearMap.Defs
public meta import Mathlib.Algebra.Module.LinearMap.Defs

public import SciLean.Algebra.IsAddGroupHom

public meta import SciLean.Algebra.IsAddGroupHom

public import SciLean.Data.IndexType

public meta import SciLean.Data.IndexType
public import SciLean.Meta.SimpAttr
public meta import SciLean.Meta.SimpAttr

public import SciLean.Tactic.AnalyzeConstLambda

public meta import SciLean.Tactic.AnalyzeConstLambda
public import SciLean.Util.SorryProof
public meta import SciLean.Util.SorryProof

@[expose] public meta section


namespace SciLean

set_option linter.unusedVariables false

section HelperTheorems

universe u'

set_option deprecated.oldSectionVars true

variable
  {X : Type u} [AddCommGroup X]
  {Y : Type v} [AddCommGroup Y]
  {Z : Type w} [AddCommGroup Z]
  {f : X → Y} (hf : IsAddGroupHom f)


theorem _root_.IsAddGroupHom.add_push (x x' : X)
  : f x + f x' = f (x + x') := by rw[hf.map_add]

theorem _root_.IsAddGroupHom.add_pull (x x' : X)
  : f (x + x') = f x + f x' := by rw[hf.map_add]

-- todo: this is not sufficiently universe polymorphic
--       and somethimes forces to write non-universe polymorphic code
--       fix this
-- theorem _root_.IsAddGroupHom.sum_push
--   {f : X → Y} (hf : IsAddGroupHom f)
--   (ι : Type) [IndexType ι] (x : ι → X)
--   : (∑ i : ι, f (x i)) = f (∑ i, x i) := by sorry_proof

-- todo: this is not sufficiently universe polymorphic
--       and somethimes forces to write non-universe polymorphic code
--       fix this
-- theorem _root_.IsAddGroupHom.sum_pull
--   {f : X → Y} (hf : IsAddGroupHom f)
--   (ι : Type) [IndexType ι] (x : ι → X)
--   : f (∑ i, x i) = ∑ i, f (x i) := by sorry_proof

theorem _root_.IsAddGroupHom.sub_push (x x' : X)
  : f x - f x' = f (x - x') := by simp[← neg_add_eq_sub,hf.map_add,hf.map_neg]

theorem _root_.IsAddGroupHom.sub_pull (x x' : X)
  : f (x - x') = f x - f x' := by simp[← neg_add_eq_sub,hf.map_add,hf.map_neg]

theorem _root_.IsAddGroupHom.neg_push (x : X)
  : - f x = f (- x) := by rw[hf.map_neg]

theorem _root_.IsAddGroupHom.neg_pull (x : X)
  : f (- x) = - f x := by rw[hf.map_neg]

theorem _root_.IsAddGroupHom.app_zero
  : f 0 = 0 := by
  have h := hf.map_add 0 0
  simp only [add_zero] at h
  exact left_eq_add.mp h

variable {g : X → Y → Z} (hg : IsAddGroupHom fun xy : X×Y => g xy.1 xy.2)

theorem _root_.IsAddGroupHom.add_push₂ (x x' : X) (y y' : Y)
  : g x y + g x' y' = g (x + x') (y + y') :=
by
  have h := hg.map_add (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsAddGroupHom.add_pull₂  (x x' : X) (y y' : Y)
  : g (x + x') (y + y') = g x y + g x' y' :=
by
  have h := hg.map_add (x,y) (x',y')
  simp at h; rw[h]

theorem _root_.IsAddGroupHom.sub_push₂ (x x' : X) (y y' : Y)
  : g x y - g x' y' = g (x - x') (y - y') :=
by
  have h := fun (x x' : X) (y y' : Y) => hg.map_add (x,y) (x',y')
  have h' := fun x y => hg.map_neg (x,y)
  simp at h; simp at h'
  simp[← neg_add_eq_sub,h,h']

theorem _root_.IsAddGroupHom.sub_pull₂  (x x' : X) (y y' : Y)
  : g (x - x') (y - y') = g x y - g x' y' :=
by
  have h := fun (x x' : X) (y y' : Y) => hg.map_add (x,y) (x',y')
  have h' := fun x y => hg.map_neg (x,y)
  simp at h; simp at h'
  simp[← neg_add_eq_sub,h,h']

theorem _root_.IsAddGroupHom.neg_push₂ (x : X) (y : Y)
  : - g x y = g (- x) (- y) :=
by
  have h := hg.map_neg (x,y)
  simp at h; rw[h]

theorem _root_.IsAddGroupHom.neg_pull₂ (x : X) (y : Y)
  : g (- x) (- y) = - g x y :=
by
  have h := hg.map_neg (x,y)
  simp at h; rw[h]

theorem _root_.IsAddGroupHom.app_zero₂
  : g 0 0 = 0 :=
by
  have h := hg.map_add (0,0) (0,0)
  simp only [Prod.mk_add_mk, add_zero] at h
  exact left_eq_add.mp h


end HelperTheorems


open Lean Meta
def generateAddGroupHomSimp
  (ctx : Array Expr) (isAddGroupHom : Expr)
  (thrmName : Name) (isSimpAttr : Bool := true) (makeSimp : Bool := false) : MetaM Unit := do

  let f := (← inferType isAddGroupHom).getArg! 4
  let data ← analyzeConstLambda f

  if data.mainArgs.size > 2 then
    throwError s!"generating simp theorems for add group hom functions in {data.mainArgs.size} arguments is not supported"

  let mut fullThrmName := (``IsAddGroupHom).append thrmName
  if data.mainArgs.size = 2 then
    fullThrmName := fullThrmName.appendAfter "₂"

  let proof ← mkAppM fullThrmName #[isAddGroupHom]
  let proof ← mkLambdaFVars ctx proof
  let statement ← inferType proof

  let thmName := data.constName |>.append (.mkSimple data.declSuffix) |>.append thrmName
  let thrmVal : TheoremVal :=
  {
    name  := thmName
    type  := statement
    value := proof
    levelParams := (collectLevelParams {} statement).params.toList
  }

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

The provided theorem should be in the simple form `IsAddGroupHom (fun x => foo x)`
Not in the composition form `IsAddGroupHom (fun x => foo (f x))`
-/
def generateAddGroupHomSimps (isAddGroupHomTheorem : Name) : MetaM Unit := do

  let info ← getConstInfo isAddGroupHomTheorem

  forallTelescope info.type fun ctx target => do
    let isAddGroupHom := mkApp (← mkConstWithFreshMVarLevels ``sorryProofAxiom) target

    let pullpush := [`add_pull,`add_push, `sub_pull,`sub_push,`neg_pull,`neg_push]

    for thrm in pullpush do
      try
        generateAddGroupHomSimp ctx isAddGroupHom thrm
      catch _ => pure ()

    let simps := [`app_zero]

    for thrm in simps do
      try
        generateAddGroupHomSimp ctx isAddGroupHom thrm (isSimpAttr:=false) (makeSimp:=true)
      catch _ => pure ()


/-- This commands generates simp lemmas for given function preserving addition and subtraction.

The commands is used as
```
#generate_add_group_hom_simps thrmName
```
where `thrmName` is a name of a theorem that states `IsAddGroupHom f`.

The command generates theorems
```
@[add_push] theorem add_push (x x' : X) : f x + f x' = f (x + x') := ...
@[add_pull] theorem add_pull (x x' : X) : f (x + x') = f x + f x' := ...
@[sub_push] theorem sub_push (x x' : X) : f x - f x' = f (x - x') := ...
@[sub_pull] theorem sub_pull (x x' : X) : f (x - x') = f x - f x' := ...
@[neg_push] theorem neg_push (x : X)    : - f x = f (- x) := ...
@[neg_pull] theorem neg_pull (x : X)    : f (- x) = - f x := ...
@[simp] theorem app_zero : f 0 = 0 := ...
```
All the above attributes are simp attributes. The ideas is that you can propagate
arithmetic operations by calling `simp` e.g. `simp only [add_pull]`.


The command also supports functions jointly linear in two arguments. If we have
`g : X → Y → Z` and `g_is_linear₂ : IsLinear K fun (x,y) => g x y` then
```
#generate_add_group_hom_simps g_is_linear₂
```
generates theorems like
```
@[add_push] theorem add_push (x x' : X) (y y' : Y) : g x y + g x' y' = g (x + x') (y + y') := ...
...
```

-/
syntax (name:=genAddGroupHomSimpsNotation) "#generate_add_group_hom_simps " ident : command

open Lean Elab Term Command
elab_rules : command
| `(#generate_add_group_hom_simps $thrm) => do
  let thmName ← resolveGlobalConstNoOverload thrm
  liftTermElabM <| generateAddGroupHomSimps thmName


-- def foo (x : ℤ) := x + x
-- def bar (x y : ℤ) := x + y

-- theorem foo_IsAddGroupHom : IsAddGroupHom (fun x => foo x) := by unfold foo; fun_prop
-- theorem bar_IsAddGroupHom : IsAddGroupHom (fun (xy : ℤ×ℤ) => bar xy.1 xy.2) := by unfold bar; fun_prop
-- theorem bar_IsAddGroupHom' : IsAddGroupHom (fun (x,y) => bar x y) := by unfold bar; fun_prop


-- #generate_add_group_hom_simps foo_IsAddGroupHom
-- #generate_add_group_hom_simps bar_IsAddGroupHom
-- #generate_add_group_hom_simps bar_IsAddGroupHom'

-- #check foo.arg_x.sum_push
-- #check bar.arg_xy.app_zero
