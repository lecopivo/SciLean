import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add


import SciLean.FunctionSpaces.Differentiable.Init

namespace SciLean


variable (R : Type _) [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]


-- structure  (f : X → Y) : Prop where
--   map_add' : ∀ x y, f (x + y) = f x + f y
--   map_smul' : ∀ (r : R) (x : X), f (r • x) = r • f x
--   cont : Continuous f := by continuity


-- Attribute and Tactic --------------------------------------------------------
--------------------------------------------------------------------------------


-- attribute
macro "differentiable" : attr =>
  `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `Differentiable):ident]))

-- tactic
macro "differentiable" : tactic =>
  `(tactic| aesop (options := { terminal := true }) (rule_sets [$(Lean.mkIdent `Differentiable):ident]))


-- Basic rules -----------------------------------------------------------------
--------------------------------------------------------------------------------

namespace Differentiable

variable 
  {R : Type _} [NontriviallyNormedField R]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace R X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace R Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace R Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace R (E i)]
  

@[differentiable]
theorem id_rule_at (x : X)
  : DifferentiableAt R (fun x : X => x) x
:= by simp


@[differentiable]
theorem id_rule
  : Differentiable R (fun x : X => x)
:= by simp
  

@[differentiable]
theorem const_rule_at (x : X) (y : Y)
  : DifferentiableAt R (fun _ : Y => x) y
:= by simp


@[differentiable]
theorem const_rule (x : X)
  : Differentiable R (fun _ : Y => x)
:= by simp


@[aesop unsafe apply (rule_sets [Differentiable])]
theorem comp_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : Y → Z) (hf : DifferentiableAt R f (g x))
  : DifferentiableAt R (fun x => f (g x)) x
:= DifferentiableAt.comp x hf hg


@[aesop safe apply (rule_sets [Differentiable])]
theorem comp_rule
  (g : X → Y) (hg : Differentiable R g)
  (f : Y → Z) (hf : Differentiable R f)
  : Differentiable R (fun x => f (g x))
:= Differentiable.comp hf hg


@[aesop unsafe apply (rule_sets [Differentiable])]
theorem let_rule_at
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : X → Y → Z) (hf : DifferentiableAt R (fun (xy : X×Y) => f xy.1 xy.2) (x, g x))
  : DifferentiableAt R (fun x => let y := g x; f x y) x := 
by 
  have h : (fun x => let y := g x; f x y) 
           = 
           (fun (xy : X×Y) => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
  rw[h]
  apply DifferentiableAt.comp
  apply hf
  apply DifferentiableAt.prod
  apply differentiableAt_id'
  apply hg


@[aesop unsafe apply (rule_sets [Differentiable])]
theorem let_rule
  (g : X → Y) (hg : Differentiable R g)
  (f : X → Y → Z) (hf : Differentiable R (fun (xy : X×Y) => f xy.1 xy.2))
  : Differentiable R (fun x => let y := g x; f x y) := 
by apply fun x => let_rule_at x g (hg x) f (hf (x, g x))


@[differentiable]
theorem pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt R (f i) x)
  : DifferentiableAt R (fun x i => f i x) x
  := by sorry


@[differentiable]
theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable R (f i))
  : Differentiable R (fun x i => f i x)
  := fun x => pi_rule_at x f (fun i => hf i x)


-- Id --------------------------------------------------------------------------
--------------------------------------------------------------------------------

@[differentiable]
theorem _root_.id.arg_a.DifferentiableAt (x : X)
  : DifferentiableAt R (id : X → X) x := by simp


@[differentiable]
theorem _root_.id.arg_a.Differentiable
  : Differentiable R (id : X → X) := by simp


-- Prod ------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- Prod.mk --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[differentiable]
theorem _root_.Prod.mk.arg_fstsnd.DifferentiableAt_comp
  (x : X)
  (g : X → Y) (hg : DifferentiableAt R g x)
  (f : X → Z) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => (g x, f x)) x
  := DifferentiableAt.prod hg hf


@[differentiable]
theorem _root_.Prod.mk.arg_fstsnd.Differentiable_comp
  (g : X → Y) (hg : Differentiable R g)
  (f : X → Z) (hf : Differentiable R f)
  : Differentiable R fun x => (g x, f x)
  := Differentiable.prod hg hf



-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[differentiable]
theorem _root_.Prod.fst.arg_self.DifferentiableAt_comp 
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => (f x).1) x
  := DifferentiableAt.fst hf


@[differentiable]
theorem _root_.Prod.fst.arg_self.Differentiable_comp 
  (f : X → Y×Z) (hf : Differentiable R f)
  : Differentiable R (fun x => (f x).1)
  := Differentiable.fst hf



-- Prod.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[differentiable]
theorem _root_.Prod.snd.arg_self.DifferentiableAt_comp 
  (x : X)
  (f : X → Y×Z) (hf : DifferentiableAt R f x)
  : DifferentiableAt R (fun x => (f x).2) x
  := DifferentiableAt.snd hf


@[differentiable]
theorem _root_.Prod.snd.arg_self.Differentiable_comp 
  (f : X → Y×Z) (hf : Differentiable R f)
  : Differentiable R (fun x => (f x).2)
  := Differentiable.snd hf



-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[differentiable]
theorem _root_.HAdd.hAdd.arg_a4a5.DifferentiableAt_comp
  (x : X) (f g : X → Y) (hf : DifferentiableAt R f x) (hg : DifferentiableAt R g x)
  : DifferentiableAt R (fun x => f x + g x) x
  := DifferentiableAt.add hf hg
 

@[differentiable]
theorem _root_.HAdd.hAdd.arg_a4a5.Differentiable_comp
  (f g : X → Y) (hf : Differentiable R f) (hg : Differentiable R g)
  : Differentiable R fun x => f x + g x
  := fun x => _root_.HAdd.hAdd.arg_a4a5.DifferentiableAt_comp x f g (hf x) (hg x)
