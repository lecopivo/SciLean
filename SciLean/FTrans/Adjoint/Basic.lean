import Mathlib.Analysis.InnerProductSpace.Adjoint

import SciLean.FunctionSpaces.ContinuousLinearMap.Basic
import SciLean.Tactic.FTrans.Basic

import SciLean.Mathlib.Analysis.InnerProductSpace.Prod
import SciLean.Profile

namespace SciLean



variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

-- noncomputable
-- def adjoint (f : X →L[K] Y) : Y →L[K] X := ContinuousLinearMap.adjoint f

instance (f : X →L[K] Y) : Dagger f (ContinuousLinearMap.adjoint f : Y →L[K] X) := ⟨⟩

@[is_continuous_linear_map, instance]
theorem t1 (f : X → Y → Z) (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2))
  : IsContinuousLinearMap K (fun xy : X×₂Y => f xy.1 xy.2) := sorry


variable   
  (g : X → Y)      (hg : IsContinuousLinearMap K g)
  (f : X → Y → Z) (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2))


#check 
  fun (z : Z) =>L[K]
    let xy := ((fun xy : X×₂Y =>L[K] f xy.1 xy.2)†) z
    let x' := ((fun x =>L[K] g x)†) xy.2
    xy.1 + x' 



#exit 
#check ContinuousLinearMap.adjoint

#check ContinuousLinearMap.adjoint_id

open InnerProduct ContinuousLinearMap

theorem adjoint.id_rule 
  : (fun (x : X) =>L[K] x)† = fun x =>L[K] x := 
by
  have h : (fun (x : X) =>L[K] x) = ContinuousLinearMap.id K X := by rfl
  rw[h]; simp

-- @[is_continuous_linear_map]
-- theorem t2
--   : IsContinuousLinearMap K (fun xy : X×₂Y => xy.2) := by (try is_continuous_linear_map); sorry

example
  (f : X → Y → Z) (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2))
  : IsContinuousLinearMap K (fun xy : X×₂Y => f xy.1 xy.2) := by is_continuous_linear_map


theorem adjoint.let_rule 
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
  rw[h]
  rw[ContinuousLinearMap.adjoint_comp]
  
  sorry

#exit 
theorem fderiv.pi_rule_at
  (x : X)
  (f : (i : ι) → X → E i) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (fderiv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := fderiv_pi hf




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
