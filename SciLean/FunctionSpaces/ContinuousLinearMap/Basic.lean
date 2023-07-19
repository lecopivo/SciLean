import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.NormedSpace.Basic

import SciLean.FunctionSpaces.ContinuousLinearMap.Init

namespace SciLean


variable (R : Type _) [Semiring R]
    {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
    {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]


structure IsContinuousLinearMap (f : X → Y) : Prop where
  map_add' : ∀ x y, f (x + y) = f x + f y
  map_smul' : ∀ (r : R) (x : X), f (r • x) = r • f x
  cont : Continuous f := by continuity


-- Attribute and Tactic --------------------------------------------------------
--------------------------------------------------------------------------------


-- attribute
macro "is_continuous_linear_map" : attr =>
  `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `IsContinuousLinearMap):ident]))

-- tactic
macro "is_continuous_linear_map" : tactic =>
  `(tactic| aesop (options := { terminal := true }) (simp_options := { enabled := false }) (rule_sets [$(Lean.mkIdent `IsContinuousLinearMap):ident, -default]))

-- add `dsimp` as a normalization step
open Lean.Meta Lean.Elab.Tactic in
@[aesop norm (rule_sets [IsContinuousLinearMap])]
def isContinuousLinearMapNormalizationTactic : TacticM Unit := do
  let goal ← inferType (Lean.Expr.mvar (← getMainGoal))
  evalTactic $ ← `(tactic| dsimp)
  let goal' ← inferType (Lean.Expr.mvar (← getMainGoal))
  if goal == goal' then
    throwError "dsimp failed to progress"



-- Lambda function notation ----------------------------------------------------
--------------------------------------------------------------------------------


def ContinuousLinearMap.mk'
  (f : X → Y) (hf : IsContinuousLinearMap R f) 
  : X →L[R] Y :=
  ⟨⟨⟨f, hf.map_add'⟩, hf.map_smul'⟩, hf.cont⟩


macro "fun " x:ident " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun $x => $b) (by is_continuous_linear_map))

macro "fun " x:ident " : " X:term " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by is_continuous_linear_map))

macro "fun " "(" x:ident " : " X:term ")" " =>L[" R:term "] " b:term : term =>
  `(ContinuousLinearMap.mk' $R (fun ($x : $X) => $b) (by is_continuous_linear_map))

@[app_unexpander ContinuousLinearMap.mk'] def unexpandContinuousLinearMapMk : Lean.PrettyPrinter.Unexpander

  | `($(_) $R $f:term $hf:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(fun $x' =>L[$R] $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(fun ($x' : $ty) =>L[$R] $b)
    | `(fun $x':ident : $ty => $b:term) => `(fun $x' : $ty =>L[$R] $b)
    | _  => throw ()
  | _  => throw ()


@[simp]
theorem ContinuousLinearMap.mk'_eval
  (x : X) (f : X → Y) (hf : IsContinuousLinearMap R f) 
  : ContinuousLinearMap.mk' R (fun x => f x) hf x = f x := by rfl


-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

namespace IsContinuousLinearMap

variable 
  {R : Type _} [Semiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
  {Z : Type _} [TopologicalSpace Z] [AddCommMonoid Z] [Module R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace (E i)] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]
  

theorem by_morphism {f : X → Y} (g : X →L[R] Y) (h : ∀ x, f x = g x) 
  : IsContinuousLinearMap R f :=
by
  have h' : f = g := by funext x; apply h
  rw[h']
  constructor
  apply g.1.1.2
  apply g.1.2
  apply g.2


  
-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem id_rule 
  : IsContinuousLinearMap R fun x : X => x 
:= 
  by_morphism (ContinuousLinearMap.id R X) (by simp)


@[is_continuous_linear_map]
theorem zero_rule 
  : IsContinuousLinearMap R fun _ : X => (0 : Y) 
:= 
  by_morphism 0 (by simp)


@[aesop unsafe apply (rule_sets [IsContinuousLinearMap])]
theorem comp_rule 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : Y → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => f (g x) 
:= 
  by_morphism ((fun y =>L[R] f y).comp (fun x =>L[R] g x)) 
  (by simp[ContinuousLinearMap.comp])


@[aesop unsafe apply (rule_sets [IsContinuousLinearMap])]
theorem let_rule 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap R (fun (xy : X×Y) => f xy.1 xy.2))
  : IsContinuousLinearMap R fun x => let y := g x; f x y
:= 
  by_morphism ((fun (xy : X×Y) =>L[R] f xy.1 xy.2).comp ((ContinuousLinearMap.id R X).prod (fun x =>L[R] g x))) 
  (by simp[ContinuousLinearMap.comp])


@[is_continuous_linear_map]
theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, IsContinuousLinearMap R (f i))
  : IsContinuousLinearMap R (fun x i => f i x) 
:=
  by_morphism (ContinuousLinearMap.pi fun i => fun x =>L[R] f i x)
  (by simp)


@[is_continuous_linear_map]
theorem morph_rule (f : X →L[R] Y) : IsContinuousLinearMap R fun x => f x := 
  by_morphism f (by simp)



end SciLean.IsContinuousLinearMap


--------------------------------------------------------------------------------

open SciLean IsContinuousLinearMap

variable 
  {R : Type _} [Semiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y]
  {Z : Type _} [TopologicalSpace Z] [AddCommMonoid Z] [Module R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, TopologicalSpace (E i)] [∀ i, AddCommMonoid (E i)] [∀ i, Module R (E i)]


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem id.arg_a.IsContinuousLinearMap
  : IsContinuousLinearMap R (id : X → X)
:= 
  by_morphism (ContinuousLinearMap.id R X) (by simp)



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem Prod.mk.arg_fstsnd.IsContinuousLinearMap_comp
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => (g x, f x)
:= 
  by_morphism ((fun x =>L[R] g x).prod (fun x =>L[R] f x)) 
  (by simp)



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem Prod.fst.arg_self.IsContinuousLinearMap
  : IsContinuousLinearMap R (@Prod.fst X Y)
:=
  by_morphism (ContinuousLinearMap.fst R X Y) 
  (by simp)


@[is_continuous_linear_map]
theorem Prod.fst.arg_self.IsContinuousLinearMap_comp
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap R f)
  : SciLean.IsContinuousLinearMap R fun (x : X) => (f x).fst
:= 
  by_morphism ((ContinuousLinearMap.fst R Y Z).comp (fun x =>L[R] f x))
  (by simp)



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem Prod.snd.arg_self.IsContinuousLinearMap
  : IsContinuousLinearMap R fun (xy : X×Y) => xy.snd
:=
  by_morphism (ContinuousLinearMap.snd R X Y) 
  (by simp)


@[is_continuous_linear_map]
theorem Prod.snd.arg_self.IsContinuousLinearMap_comp
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap R f)
  : SciLean.IsContinuousLinearMap R fun (x : X) => (f x).snd
:= 
  by_morphism ((ContinuousLinearMap.snd R Y Z).comp (fun x =>L[R] f x))
  (by simp)



-- Neg.neg ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[is_continuous_linear_map]
theorem Neg.neg.arg_a2.IsContinuousLinearMap_comp 
  {R : Type _} [Ring R]
  {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [TopologicalAddGroup Y]
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => - f x
:= 
  by_morphism (ContinuousLinearMap.neg.neg (fun x =>L[R] f x))
  (by simp[ContinuousLinearMap.neg])



-- HAdd.hAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[is_continuous_linear_map]
theorem HAdd.hAdd.arg_a4a5.IsContinuousLinearMap_comp [ContinuousAdd Y]
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x + g x
:= 
  by_morphism (ContinuousLinearMap.add.add (fun x =>L[R] f x) (fun x =>L[R] g x))
  (by simp[ContinuousLinearMap.add])



-- HSub.hSub -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[is_continuous_linear_map]
theorem HSub.hSub.arg_a4a5.IsContinuousLinearMap_comp 
  {R : Type _} [Ring R]
  {X : Type _} [TopologicalSpace X] [AddCommGroup X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommGroup Y] [Module R Y] [TopologicalAddGroup Y]
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x - g x
:= 
  by_morphism (ContinuousLinearMap.sub.sub (fun x =>L[R] f x) (fun x =>L[R] g x))
  (by simp[ContinuousLinearMap.sub])



-- HMul.hMul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

def ContinuousLinearMap.mul_left 
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [Semiring X] [Algebra R X] [TopologicalSemiring X] 
  (x' : X) 
  : X →L[R] X := 
  ⟨⟨⟨fun x => x' * x, 
    by apply mul_add⟩, 
    by simp⟩, 
    by continuity⟩


def ContinuousLinearMap.mul_right 
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [Semiring X] [Algebra R X] [TopologicalSemiring X] 
  (x' : X) 
  : X →L[R] X := 
  ⟨⟨⟨fun x => x * x', 
    fun a b => add_mul a b x'⟩, 
    by simp⟩, 
    by continuity⟩


@[is_continuous_linear_map]
theorem HMul.hMul.arg_a4.IsContinuousLinearMap_comp
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra R Y] [TopologicalSemiring Y] 
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  (y' : Y) 
  : IsContinuousLinearMap R fun x => f x * y'
:= 
  by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_right y') (fun x =>L[R] f x))
  (by simp[ContinuousLinearMap.mul_right])


@[is_continuous_linear_map]
theorem HMul.hMul.arg_a5.IsContinuousLinearMap_comp
  {R : Type _} [CommSemiring R] 
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [Semiring Y] [Algebra R Y] [TopologicalSemiring Y] 
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  (y' : Y) 
  : IsContinuousLinearMap R fun x => y' * f x
:= 
  by_morphism (ContinuousLinearMap.comp (ContinuousLinearMap.mul_left y') (fun x =>L[R] f x))
  (by simp[ContinuousLinearMap.mul_left])



-- Smul.smul ---------------------------------------------------------------------
-------------------------------------------------------------------------------- 

/-- Creates `fun x =>L[R] r • g x` -/
def ContinuousLinearMap.smulLeft 
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y] [ContinuousConstSMul R Y]
  (g : X →L[R] Y)
  (r : R) 
  : X →L[R] Y := 
  let f : Y →L[R] Y := 
    ⟨⟨⟨fun x => r • x, 
      DistribMulAction.smul_add r⟩, 
      smul_comm r⟩, 
      ContinuousConstSMul.continuous_const_smul r⟩
  f.comp g


@[simp]
def ContinuousLinearMap.smul_left 
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y] [ContinuousConstSMul R Y]
  (g : X →L[R] Y)
  (r : R) (x : X)
  : smulLeft g r x = r • g x := by rfl


@[is_continuous_linear_map]
theorem Smul.smul.arg_a3.IsContinuousLinearMap_comp 
  [TopologicalSpace R] [ContinuousSMul R Y]
  (f : X → R) (hf : IsContinuousLinearMap R f)
  (y : Y) 
  : IsContinuousLinearMap R fun x => f x • y
:= 
  by_morphism (ContinuousLinearMap.smulRight (fun x =>L[R] f x) y)
  (by simp)


@[is_continuous_linear_map]
theorem Smul.smul.arg_a4.IsContinuousLinearMap_comp 
  {R : Type _} [CommSemiring R]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  {Y : Type _} [TopologicalSpace Y] [AddCommMonoid Y] [Module R Y] [ContinuousConstSMul R Y]
  (c : R)
  (f : X → Y) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => c • f x
:= 
  by_morphism (ContinuousLinearMap.smulLeft (fun x =>L[R] f x) c)
  (by simp)



-- HDiv.hDiv -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

/-- Creates `fun x =>L[R] g x / y` -/
def ContinuousLinearMap.divRight
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  (g : X →L[R] K) (y : K) 
  : X →L[R] K := 
  let f : K →L[R] K := 
    ⟨⟨⟨fun x => x / y, 
      by apply fun a b => add_div a b y⟩, 
      by intro r x; simp; (repeat rw[div_eq_inv_mul]); apply mul_smul_comm⟩, 
      by continuity⟩
  f.comp g


@[simp]
def ContinuousLinearMap.div_right
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  (g : X →L[R] K) (y : K) (x : X)
  : divRight g y x = g x / y := by rfl


@[is_continuous_linear_map]
theorem HDiv.hDul.arg_a4.IsContinuousLinearMap_comp
  {R : Type _} [NontriviallyNormedField R]
  {K : Type _} [NontriviallyNormedField K] [NormedAlgebra R K]
  {X : Type _} [TopologicalSpace X] [AddCommMonoid X] [Module R X]
  (f : X → K) (hf : IsContinuousLinearMap R f) (y : K) 
  : IsContinuousLinearMap R fun x => f x / y
:= 
  by_morphism (ContinuousLinearMap.divRight (fun x =>L[R] f x) y)
  (by simp)
