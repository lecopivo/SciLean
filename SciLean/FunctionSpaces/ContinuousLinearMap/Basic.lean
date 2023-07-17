import Mathlib.Topology.Algebra.Module.Basic

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
  `(tactic| aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `IsContinuousLinearMap):ident]))



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
theorem scomb_rule 
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap R (fun (xy : X×Y) => f xy.1 xy.2))
  : IsContinuousLinearMap R fun x => f x (g x) 
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



-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem _root_.id.arg_a.IsContinuousLinearMap
  : IsContinuousLinearMap R (id : X → X)
:= 
  by_morphism (ContinuousLinearMap.id R X) (by simp)



-- Prod.mk ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem _root_.Prod.mk.arg_fstsnd.IsContinuousLinearMap_comp
  (g : X → Y) (hg : IsContinuousLinearMap R g)
  (f : X → Z) (hf : IsContinuousLinearMap R f)
  : IsContinuousLinearMap R fun x => (g x, f x)
:= 
  by_morphism ((fun x =>L[R] g x).prod (fun x =>L[R] f x)) 
  (by simp)


-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem _root_.Prod.fst.arg_self.IsContinuousLinearMap
  : IsContinuousLinearMap R (@Prod.fst X Y)
:=
  by_morphism (ContinuousLinearMap.fst R X Y) 
  (by simp)


@[is_continuous_linear_map]
theorem _root_.Prod.fst.arg_self.IsContinuousLinearMap_comp
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap R f)
  : SciLean.IsContinuousLinearMap R fun (x : X) => (f x).fst
:= 
  by_morphism ((ContinuousLinearMap.fst R Y Z).comp (fun x =>L[R] f x))
  (by simp)



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[is_continuous_linear_map]
theorem _root_.Prod.snd.arg_self.IsContinuousLinearMap
  : IsContinuousLinearMap R fun (xy : X×Y) => xy.snd
:=
  by_morphism (ContinuousLinearMap.snd R X Y) 
  (by simp)


@[is_continuous_linear_map]
theorem _root_.Prod.snd.arg_self.IsContinuousLinearMap_comp
  (f : X → Y×Z) (hf : SciLean.IsContinuousLinearMap R f)
  : SciLean.IsContinuousLinearMap R fun (x : X) => (f x).snd
:= 
  by_morphism ((ContinuousLinearMap.snd R Y Z).comp (fun x =>L[R] f x))
  (by simp)



-- HAdd.hAdd -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[is_continuous_linear_map]
theorem _root_.HAdd.hAdd.arg_a4a5.IsContinuousLinearMap_comp
  (f g : X → Y) (hf : IsContinuousLinearMap R f) (hg : IsContinuousLinearMap R g)
  : IsContinuousLinearMap R fun x => f x + g x
:= 
  sorry
