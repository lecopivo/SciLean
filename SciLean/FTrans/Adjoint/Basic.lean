import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

import SciLean.FunctionSpaces.ContinuousLinearMap.Basic
import SciLean.FunctionSpaces.ContinuousLinearMap.Notation

import SciLean.Tactic.FTrans.Basic

import SciLean.Mathlib.Analysis.InnerProductSpace.Prod
import SciLean.Profile


variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- TODO: move to mathlib
instance {E : ι → Type _} [∀ i, UniformSpace (E i)] [∀ i, CompleteSpace (E i)] : CompleteSpace (PiLp 2 E) := by unfold PiLp; infer_instance


-- Set up custom notation for adjoint. Mathlib's notation for adjoint seems to be broken
instance (f : X →L[K] Y) : SciLean.Dagger f (ContinuousLinearMap.adjoint f : Y →L[K] X) := ⟨⟩
variable (g : X → Y) (hg : SciLean.IsContinuousLinearMap K g)

example 
  : SciLean.IsContinuousLinearMap K fun (xy : X×₂Y) => xy.1 + (fun x =>L[K] g x)† xy.2 := by fprop

-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------
namespace  ContinuousLinearMap.adjoint

open SciLean

theorem id_rule 
  : (fun (x : X) =>L[K] x)† = fun x =>L[K] x := 
by
  have h : (fun (x : X) =>L[K] x) = ContinuousLinearMap.id K X := by rfl
  rw[h]; simp


theorem const_rule 
  : (fun (x : X) =>L[K] (0 : Y))† = fun x =>L[K] 0 := 
by
  sorry

theorem prod_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Z) (hf : IsContinuousLinearMap K f)
  : ((fun x =>L[K] (g x, f x)) : X →L[K] Y×₂Z)†
    =
    fun yz : Y×₂Z =>L[K]
      let x₁ := (fun x =>L[K] g x)† yz.1
      let x₂ := (fun x =>L[K] f x)† yz.2
      x₁ + x₂ := 
by 
  sorry


theorem comp_rule 
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : Y → Z) (hf : IsContinuousLinearMap K f)
  : (fun x =>L[K] f (g x))†
    =
    fun z =>L[K]
      let y := (fun y =>L[K] f y)† z
      let x := (fun x =>L[K] g x)† y
      x := 
by
  have h : (fun x =>L[K] f (g x))
           =
           (fun y =>L[K] f y).comp (fun x =>L[K] g x)
         := by rfl
  rw[h]
  rw[ContinuousLinearMap.adjoint_comp]
  ext dx; simp


theorem let_rule 
  (g : X → Y)      (hg : IsContinuousLinearMap K g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2))
  : (fun x =>L[K] let y := g x; f x y)†
    =
    fun z =>L[K]
      let xy := ((fun xy : X×₂Y =>L[K] f xy.1 xy.2)†) z
      let x' := ((fun x =>L[K] g x)†) xy.2
      xy.1 + x' := 
by
  have h : (fun x =>L[K] let y := g x; f x y)
           =
           (fun xy : X×₂Y =>L[K] f xy.1 xy.2).comp (fun x =>L[K] (x, g x))
         := by rfl
  rw[h, ContinuousLinearMap.adjoint_comp]
  have h' : ((fun x =>L[K] (x, g x)) : X →L[K] X×₂Y)† 
            = 
            (fun (xy : X×₂Y) =>L[K] xy.1 + (fun x =>L[K] g x)† xy.2)
          := by rw[prod_rule (fun x => x) (by fprop) g hg]; simp[id_rule]
  rw[h']; rfl


#exit

example : CompleteSpace ((i :ι) → E i) := by infer_instance

open BigOperators

set_option trace.Meta.Tactic.fprop.discharge true in
theorem pi_rule
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, IsContinuousLinearMap K (f i))
  : ((fun (x : X) =>L[K] fun (i : ι) => f i x) : X →L[K] PiLp 2 E)†
    = 
    (fun x' =>L[K] ∑ i, (fun x =>L[K] f i x)† (x' i))
  := sorry

#exit


noncomputable
def a := (fun (x : X) =>L[K] x)† 

#check (fun (x : X) =>L[K] x)†

#check a†

def ProdLp (r : ℝ) (α β : Type _) := α × β

#check ((1,2) : ProdLp 2 Nat Nat)

instance 
  {K : Type _}
  {X : Type _} [Inner K X]
  {Y : Type _} [Inner K Y]
  : Inner K (X × Y) := sorry


instance
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y]
  : InnerProductSpace K (X × Y) where
  norm_sq_eq_inner := sorry
  conj_symm := sorry
  add_left := sorry
  smul_left := sorry

noncomputable
def b := ContinuousLinearMap.adjoint (fun xy : X×Y =>L[K] f xy.1 xy.2)


noncomputable
def c := ContinuousLinearMap.adjoint (ContinuousLinearMap.mk' K (fun xy : X×Y => f xy.1 xy.2) sorry)

#check c

example :
   (@IsContinuousLinearMap K DivisionSemiring.toSemiring (Prod X Y) instTopologicalSpaceProd Prod.instAddCommMonoidSum
       Prod.module Z UniformSpace.toTopologicalSpace AddCommGroup.toAddCommMonoid NormedSpace.toModule fun xy =>
       f xy.fst xy.snd)
    =
    (@IsContinuousLinearMap K DivisionSemiring.toSemiring (Prod X Y) UniformSpace.toTopologicalSpace
        AddCommGroup.toAddCommMonoid NormedSpace.toModule Z UniformSpace.toTopologicalSpace AddCommGroup.toAddCommMonoid
        NormedSpace.toModule fun xy => f xy.fst xy.snd)
   := by rfl

def hoh : InnerProductSpace K (X×Y) := by infer_instance

#print hoh


#check instTopologicalSpaceProd
#check instUniformSpaceProd
#exit

theorem adjoint.let_rule
  (g : X → Y) (hg : IsContinuousLinearMap K g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2))
  (z : Z)
  : ((fun x : X =>
        let y := g x
        f x y)† z)
    =
      let f' := (fun xy : X×Y =>L[K] f xy.1 xy.2)†
      let g' := (fun x =>L[K] g x)†
      let xy := f' z
      let x' := g' xy.2
      x + x' :=  sorry
-- by 
--   have h : (fun x => f x (g x)) = (fun xy : X×Y => f xy.1 xy.2) ∘ (fun x => (x, g x)) := by rfl
--   rw[h]
--   rw[fderiv.comp x hf (DifferentiableAt.prod (by simp) hg)]
--   rw[DifferentiableAt.fderiv_prod (by simp) hg]
--   ext dx; simp[ContinuousLinearMap.comp]
--   rfl
#exit
theorem fderiv.pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (fderiv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := fderiv_pi hf


theorem fderiv.pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (fderiv K fun (x : X) (i : ι) => f i x)
    = 
    fun x => fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := by funext x; apply fderiv_pi (fun i => hf i x)
