import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.VecDiffeology
import SciLean.Analysis.Diffeology.Option
import SciLean.Analysis.Diffeology.Pi
import SciLean.Analysis.Diffeology.ArrayTangentSpace

import SciLean.Analysis.Calculus.ContDiff
import SciLean.Algebra.IsLinearMap
import SciLean.Tactic.IfPull

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

-- todo: move this
@[simp]
theorem heq_cast_rhs {α β} (h : α = β) (x y : α) :
  x = y → HEq x (cast h y) := by intro h'; subst h h'; rfl

-- todo: move this
@[simp]
theorem heq_cast_lhs {α β} (h : α = β) (x y : α) :
  x = y → HEq (cast h x) y := by intro h'; subst h h'; rfl

open Diffeology in
instance (X : Type*) [Diffeology X] : Diffeology (Array X) where

  Plot n := (s : ℕ) × ((i : Fin s) → Plot X n)
  plotEval := fun ⟨s,p⟩ u => .ofFn (fun i : Fin s => p i u)

  plot_ext := by
    intro n ⟨s,p⟩ ⟨s',q⟩
    simp; intro h
    sorry

  plotComp := fun {n m} ⟨d,p⟩ {f} hf =>  ⟨d, fun i => plotComp (p i) hf⟩
  plotComp_eval := by simp

  constPlot n x := ⟨x.size, fun i => constPlot n x[i]⟩
  constPlot_eval := by intro n x u; simp; ext <;> simp


variable {X : Type*} [Diffeology X]

open Diffeology

@[simp]
theorem array_plot_eval (s : ℕ) (p : (i : Fin s) → Plot X n) :
  ((show Plot (Array X) n from ⟨s,p⟩) : ℝ^n → Array X)
  =
  fun u : ℝ^n => Array.ofFn (fun i => p i u) := by rfl

@[simp]
theorem array_plot_eval_size (p : Plot (Array X) n) (u : ℝ^n) :
    (p u).size = p.1 := by
  cases p; simp


section TangenSpaceMap
open TangentSpace

variable {X : Type*} [Diffeology X]
    {TX : outParam (X → Type*)} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]


def tsArrayMap' :
    (s : ℕ) × (Fin s → (x : X) × ((Fin n → ℝ) →ₗ[ℝ] TX x))
    ≃
    (Σ x : Array X, (ℝ^n →ₗ[ℝ] ArrayTangentSpace x)) where

  toFun := fun ⟨s,p⟩ =>
    let x := Array.ofFn (fun i => (p i).1)
    ⟨x,
     LinearMap.mk' ℝ
       (fun du => (ArrayTangentSpace.ofFnCast (fun i => (p i).2 du) (by simp[x]) (by simp[x])))
       sorry⟩
  invFun := fun ⟨x,dx⟩ =>
    ⟨x.size,
     fun i => ⟨x[i], LinearMap.mk' ℝ (fun u => (dx u).get i) sorry⟩⟩
  left_inv := by
    intro ⟨s,p⟩;
    simp
    sorry
  right_inv := by
    intro ⟨x,dx⟩
    simp
    sorry


def tsArrayMap :
    (s : ℕ) × (Fin s → (x : X) × (TX x))
    ≃
    (Σ x : Array X, ArrayTangentSpace x) where

  toFun := fun ⟨s,p⟩ =>
    let x := Array.ofFn (fun i => (p i).1)
    ⟨x,
     ArrayTangentSpace.ofFnCast (fun i => (p i).2) (by simp[x]) (by simp[x])⟩
  invFun := fun ⟨x,dx⟩ => ⟨x.size, fun i => ⟨x[i], dx.get i⟩⟩
  left_inv := by
    intro ⟨s,p⟩
    simp
    sorry
  right_inv := by
    intro ⟨x,dx⟩
    simp
    sorry

omit [Diffeology X] [(x : X) → AddCommGroup (TX x)] [(x : X) → Module ℝ (TX x)] [TangentSpace X TX] in
theorem ts_array_ext (xdx xdx' : (s : ℕ) × (Fin s → (x : X) × (TX x))) :
  (h : xdx.1 = xdx'.1) → (∀ i : Fin xdx.1, xdx.2 i = xdx'.2 ⟨i.1,by omega⟩) → xdx = xdx' := by
  cases xdx; cases xdx'
  simp; intro h; subst h; intro h
  simp; funext i; simp_all

@[simp]
theorem fst_tsArrayMap'
   (sp : (s : ℕ) × (Fin s → (x : X) × ((Fin n → ℝ) →ₗ[ℝ] TX x))) :
   (tsArrayMap' sp).fst = Array.ofFn (fun i => (sp.2 i).1) := by rfl

@[simp]
theorem fst_tsArrayMap_symm
   (xdx : Σ x : Array X, ArrayTangentSpace x) :
   (tsArrayMap.symm xdx).fst = xdx.1.size := by rfl

@[simp]
theorem snd_tsArrayMap_symm
   (xdx : Σ x : Array X, ArrayTangentSpace x) (i) :
   (tsArrayMap.symm xdx).snd i = ⟨xdx.1[i], xdx.2.get i⟩ := by rfl

@[simp]
theorem tsArrayMap'_symm_duality
   (xdx : Σ x : Array X, ArrayTangentSpace x) :
   (tsArrayMap'.symm (duality xdx)) = ⟨xdx.1.size, fun i => duality ⟨xdx.1[i], xdx.2.get i⟩⟩ := by
  cases xdx
  simp[duality]
  simp[tsArrayMap']

@[simp]
theorem tsArrayMap_symm_duality_symm_tsArrayMap'
    (s : ℕ) (p : Fin s → (x : X) × (ℝ^1 →ₗ[ℝ] (TX x))) :
    tsArrayMap.symm (duality.symm (tsArrayMap' ⟨s,p⟩))
    =
    ⟨s, fun i => duality.symm (p i)⟩ := by
  apply tsArrayMap.injective
  simp
  simp[duality]
  simp[tsArrayMap',tsArrayMap]

end TangenSpaceMap


open TangentSpace

noncomputable
instance (X : Type*) [Diffeology X]
    {TX : outParam (X → Type*)} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    : TangentSpace (Array X) (fun x => ArrayTangentSpace x) where

  tangentMap := fun {n} ⟨s,p⟩ u => tsArrayMap' ⟨s, fun i => tangentMap (p i) u⟩

  tangentMap_const := by
    intro n x u
    apply tsArrayMap'.symm.injective
    simp
    simp[tsArrayMap']

  tangentMap_fst := by
    intro n ⟨s,p⟩ u
    simp

  exp xdx :=
    let ⟨s,xdx⟩ := tsArrayMap.symm xdx
    ⟨s, fun i => exp (xdx i)⟩

  exp_at_zero := by
    intro ⟨x,dx⟩
    simp
    ext <;> simp

  tangentMap_exp_at_zero := by
    intro ⟨x,dx⟩
    apply tsArrayMap'.symm.injective
    simp


variable
  {X : Type*} [Diffeology X] {TX : outParam (X → Type*)}
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]


@[simp]
theorem array_exp_fst (xdx : Σ x : Array X, ArrayTangentSpace x) :
    (exp xdx).1 = xdx.1.size := by rfl


----------------------------------------------------------------------------------------------------
-- Array.get? --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


@[fun_prop]
theorem Array.get?.arg_a.DSmooth_rule (i : ℕ) : DSmooth (fun x : Array X => x[i]?) := by
  constructor
  existsi (fun n ⟨s,p⟩ =>
            if h : i < s then
              .some (p ⟨i,h⟩)
            else
              .none)
  intros dim u p;
  cases p; simp
  split_ifs with h <;> simp[h,getElem?_def]



@[simp]
theorem plotMap_get? (i : ℕ) (p : Plot (Array X) n) :
    (fun x : Array X => x[i]?) ∘ₚ p
    =
    if h : i < p.1 then
      .some (p.2 ⟨i,h⟩)
    else
      none := by
  apply plot_ext; intro u
  cases p; simp
  split_ifs with h <;> simp[h,getElem?_def]


@[fun_prop]
theorem Array.get?.arg_a.TSSmooth (i : ℕ) :
    TSSmooth (fun x : Array X => x[i]?) where

  toDSmooth := by fun_prop

  plot_independence := by
    intro n ⟨s,p⟩ ⟨r,q⟩ u h
    have hsize := (h rewrite_type_by simp[tangentMap]).1
    subst hsize
    simp[tangentMap] at h ⊢
    split_ifs with hi
    · simp; exact congrFun h ⟨i,hi⟩
    · rfl


@[fun_trans]
theorem Array.get?.arg_a.fwdTSDeriv_rule (i : ℕ) :
   fwdTSDeriv (fun x : Array X => x[i]?)
   =
   fun xdx =>
     if hi : i < xdx.1.size then
       let i : Fin _ := ⟨i,hi⟩
       ⟨xdx.1[i], xdx.2.get i⟩
     else
       ⟨none, 0⟩ := by
  funext ⟨x,dx⟩
  rw[fwdTSDeriv_def (by fun_prop)]
  simp (disch:=fun_prop)

  have hsize : x.size = (exp ⟨x,dx⟩).fst := by simp[exp]

  by_cases hi : i < x.size <;> (
    have hi' := hi rewrite_type_by rw[hsize]
    simp[hi,hi']
    apply tsOptionMap.symm.injective
    simp[exp, tangentMap]
  )


----------------------------------------------------------------------------------------------------
-- Array.append ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.Array.append.arg_asbs.DSmooth_rule :
    DSmooth (fun x : Array X×Array X => x.1 ++ x.2) := by
  constructor
  existsi (fun n (⟨s,p⟩,⟨r,q⟩) =>
            ⟨s+r, fun i => if h : i < s then p ⟨i.1,h⟩ else q ⟨i.1-s,by omega⟩⟩)
  intros dim u p;
  cases' p with p q
  cases' p with s p
  cases' q with r q
  simp; ext i
  · simp
  · simp[Array.getElem_append]
    split_ifs <;> simp


@[simp]
theorem plotMap_append (p : Plot (Array X × Array X) n) :
    (fun x : Array X×Array X => x.1 ++ x.2) ∘ₚ p
    =
    ⟨p.1.1 + p.2.1,
    fun i => if h : i < p.1.1 then p.1.2 ⟨i.1,h⟩ else p.2.2 ⟨i.1-p.1.1,by omega⟩⟩ := by
  cases' p with p q
  cases' p with s p
  cases' q with r q
  simp; ext i
  · simp
  · simp[Array.getElem_append]
    split_ifs <;> simp


@[fun_prop]
theorem ContDiff.differentiableAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (hf : ContDiff ℝ ⊤ f) (x : X) : DifferentiableAt ℝ f x := by
  fun_prop (config:={maxTransitionDepth:=5})


@[fun_prop]
theorem _root_.Array.append.arg_asbs.TSSmooth_rule :
    TSSmooth (fun x : Array X×Array X => x.1 ++ x.2) where
  toDSmooth := by fun_prop
  plot_independence := by
    intro n p q u
    rcases p with ⟨⟨s,_⟩,⟨_,_⟩⟩
    rcases q with ⟨⟨_,_⟩,⟨_,_⟩⟩
    intro h
    have hsize₁ := (h rewrite_type_by simp[tangentMap]).1.1
    have hsize₂ := (h rewrite_type_by simp[tangentMap]).2.1
    subst hsize₁; subst hsize₂
    simp
    apply tsArrayMap'.symm.injective
    simp[tangentMap] at h ⊢
    funext i
    split_ifs
    · simp[congrFun h.1 ⟨i,by omega⟩]
    · simp[congrFun h.2 ⟨i.1-s,by have := i.2; omega⟩]


@[fun_trans]
theorem _root_.Array.append.arg_asbs.fwdTSDeriv_rule :
    fwdTSDeriv (fun x : Array X×Array X => x.1 ++ x.2)
    =
    fun xdx =>
      let p := xdx.1.1
      let q := xdx.1.2
      let dp := xdx.2.1
      let dq := xdx.2.2
      ⟨p++q, dp.append dq⟩ := by
  funext xdx
  rcases xdx with ⟨⟨x,y⟩,⟨dx,dy⟩⟩
  rw[fwdTSDeriv_def (by fun_prop)]
  simp[tangentMap]
  rw[plotMap_append]
  simp
  apply tsArrayMap.symm.injective
  simp
  apply ts_array_ext
  · simp
    intro i
    split_ifs with h <;>
      simp[exp,Array.getElem_append,ArrayTangentSpace.get_append,h]
  · simp



----------------------------------------------------------------------------------------------------
-- Array.append ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem _root_.Array.setD.arg_av.DSmooth_rule (i : ℕ) :
    DSmooth (fun x : Array X×X => x.1.setD i x.2) := by

  constructor
  existsi (fun n (⟨s,p⟩,q) =>
    if i < s then
      ⟨s, fun j => if i = j then q else p j⟩
    else
      ⟨s,p⟩)
  intro n u ⟨⟨s,p⟩,q⟩
  dsimp
  split_ifs with hi
  case neg => simp[Array.setD,hi]
  case pos =>
    ext j h₁ h₂
    · simp
    · simp[Array.setD,hi,Array.getElem_set]
      split_ifs <;> rfl


@[simp]
theorem plotMap_setD (i : ℕ) (p : Plot (Array X × X) n) :
    (fun x : Array X×X => x.1.setD i x.2) ∘ₚ p
    =
    if i < p.1.1 then
      ⟨p.1.1, fun j => if i = j then p.2 else p.1.2 j⟩
    else
      p.1 := by

  rcases p with ⟨⟨s,p⟩,q⟩
  ext u j
  · dsimp; split_ifs <;> simp
  · dsimp
    split_ifs with hi
    · simp[Array.setD,hi,Array.getElem_set]
      split_ifs <;> rfl
    · simp[Array.setD,hi,Array.getElem_set]


@[fun_prop]
theorem _root_.Array.setD.arg_av.TSSmooth_rule (i : ℕ) :
    TSSmooth (fun x : Array X×X => x.1.setD i x.2) := by

  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u
    rcases p with ⟨⟨s,_⟩,_⟩
    rcases q with ⟨⟨_,_⟩,_⟩
    intro h
    have hsize₁ := (h rewrite_type_by simp[tangentMap]).1.1
    subst hsize₁
    have h₁ := (h rewrite_type_by simp[tangentMap]).1
    have h₂ := (h rewrite_type_by simp[tangentMap]).2
    simp only [plotMap_setD]
    split_ifs with hi
    · simp[tangentMap]
      funext j
      split_ifs
      · exact h₂
      · exact congrFun h₁ j
    · simp[tangentMap,h₁]


def ArrayTangentBundle.setD (xdx : Σ x : Array X, ArrayTangentSpace x) (i : ℕ) (xdxi : Σ x, TX x) :
    Σ x : Array X, ArrayTangentSpace x :=
  let x  := xdx.1
  let dx := xdx.2
  let xi  := xdxi.1
  let dxi := xdxi.2
  ⟨x.setD i xi,
   { data := dx.data.setD i ⟨_, dxi⟩
     data_size := by simp[dx.data_size]
     data_cast := sorry_proof
   }⟩


@[fun_trans]
theorem _root_.Array.setD.arg_av.fwdTSDeriv (i : ℕ) :
    fwdTSDeriv (fun x : Array X×X => x.1.setD i x.2)
    =
    fun xdx =>
      let x  := xdx.1.1
      let xi := xdx.1.2
      let dx  := xdx.2.1
      let dxi := xdx.2.2
      ArrayTangentBundle.setD ⟨x,dx⟩ i ⟨xi,dxi⟩ := by

  funext xdx
  rcases xdx with ⟨⟨x,xi⟩,⟨dx,dxi⟩⟩
  rw[fwdTSDeriv_def (by fun_prop)]; dsimp
  rw[plotMap_setD]; dsimp
  split_ifs with hi
  · sorry
  · simp
    apply tsArrayMap.symm.injective
    apply ts_array_ext
    · intro j
      simp[tsArrayMap,ArrayTangentBundle.setD]
      simp[Array.setD,hi,ArrayTangentSpace.get]
      have hi' : ¬(i < dx.data.size) := sorry

      conv => enter[2,2]; simp[hi']
      sorry
    · simp[tsArrayMap,ArrayTangentBundle.setD]
