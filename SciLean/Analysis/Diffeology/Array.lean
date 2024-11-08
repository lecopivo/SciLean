import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.VecDiffeology
import SciLean.Analysis.Diffeology.Option
import SciLean.Analysis.Calculus.ContDiff
import SciLean.Data.ArrayN

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ


@[ext]
structure ArrayPlot (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (n : ℕ) where
  dim : ℕ
  val : ℝ^n → ArrayN X dim
  contDiff : ContDiff ℝ ⊤ val


open Diffeology in
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Diffeology (Array X) where

  Plot n := ArrayPlot X n

  plotEval p u := (p.val u).1

  plot_ext := by
    intro n ⟨dim,p,_⟩ ⟨dim',q,_⟩
    simp; intro h
    have h := fun u => congrFun h u
    have hn : dim = dim' := by rw [(p 0).2]; rw [(q 0).2]; rw[h 0]
    subst hn
    simp
    funext u
    apply ArrayN.ext_data;
    exact h u

  plotComp {n m} p {f} hf := {
    dim := p.dim
    val := fun x => p.val (f x)
    contDiff := by
      have := p.contDiff
      fun_prop
  }

  plotComp_eval := by simp

  constPlot n x := {
    dim := x.size
    val := fun _ => ArrayN.mk x rfl
    contDiff := by fun_prop
  }

  constPlot_eval := by simp

open Diffeology
variable {X} [NormedAddCommGroup X] [NormedSpace ℝ X]

@[fun_prop]
theorem plot_val_contDiff (p : Plot (Array X) n) : ContDiff ℝ ⊤ p.val := p.contDiff

@[simp]
theorem plot_eval (n dim : ℕ) (f : ℝ^n → ArrayN X dim) (hf : ContDiff ℝ ⊤ f) :
  (show Plot (Array X) n from ArrayPlot.mk dim f hf) = fun u => (f u).1 := by rfl

@[fun_prop]
def _root_.SciLean.ArrayN.sizeCast.arg_a.IsContinuousLinearMap {m} (h : n = m := by simp_all) :
    IsContinuousLinearMap ℝ (fun x : ArrayN X n => x.sizeCast h):= by
  subst h; simp[ArrayN.sizeCast]; apply IsContinuousLinearMap.id_rule

open TangentSpace


def tsMap' {U} [AddCommGroup U] [Module ℝ U] {n}
    (x : Array X) (dx : U →ₗ[ℝ] ArrayN X n) (hn : n = x.size) : Σ x : Array X, (U →ₗ[ℝ] ArrayN X x.size) :=
  ⟨x, fun u =>ₗ[ℝ] (dx u).sizeCast hn⟩

def tsMapInv' {U} [AddCommGroup U] [Module ℝ U]
    (x : Σ x : Array X, (U →ₗ[ℝ] ArrayN X x.size)) : Σ n, Array X × (U →ₗ[ℝ] ArrayN X n) :=
  ⟨x.1.size, (x.1, fun u =>ₗ[ℝ] (x.2 u))⟩

@[simp]
theorem tsMapInv'_tsMap {U} [AddCommGroup U] [Module ℝ U] {n}
    (x : Array X) (dx : U →ₗ[ℝ] ArrayN X n) (hn : n = x.size) :
    tsMapInv' (tsMap' x dx hn) = ⟨n,(x,dx)⟩ := by
  simp[tsMapInv',tsMap']; subst hn; simp[ArrayN.sizeCast]
  ext u; simp


def tsMap'_ext {U} [AddCommGroup U] [Module ℝ U] {n}
    (x y : Array X) (dx dy : U →ₗ[ℝ] ArrayN X n) (hx : n = x.size) (hy : n = y.size) :
  x = y → dx = dy → tsMap' x dx hx = tsMap' y dy hy := by simp_all



noncomputable
instance (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    TangentSpace (Array X) (fun x => ArrayN X x.size) where

  tangentMap := fun {n} ⟨dim,p,_⟩ u => tsMap' (p u).1 (fderiv ℝ p u).1 (by simp_all)

  exp := fun ⟨x,dx⟩ => ⟨x.size, fun t => x.fixSize + t 0 • dx, by fun_prop⟩
  tangentMap_const := by intro n x u; simp; simp[tsMap',ArrayN.sizeCast]
  tangentMap_fst := by intro n ⟨_,x,_⟩ u; simp[tsMap']
  exp_at_zero := by intro ⟨_,u⟩; cases u; simp[Array.fixSize]
  tangentMap_exp_at_zero := by
    intro ⟨_,u⟩; fun_trans; rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] -- [Diffeology X] [StandardDiffeology X]


@[simp]
theorem arrayPlot_get_fin (p : Plot (Array X) n) (u : ℝ^n) (i : Fin (p u).size) :
  (p u)[i] = (p.val u)[⟨i, by rw[(p.val u).2]; exact i.2⟩] := by rfl

@[simp]
theorem arrayPlot_get_int (p : Plot (Array X) n) (u : ℝ^n) (i : ℕ) (hi : i < (p u).size) :
  (p u)[i] = (p.val u)[⟨i, by rw[(p.val u).2]; exact hi⟩] := by rfl

@[simp]
theorem arrayPlot_size (p : Plot (Array X) n) (u : ℝ^n) :
  (p u).size = p.dim := by rw[(p.val u).2]; rfl

@[simp]
theorem arrayPlot_get? (p : Plot (Array X) n) (i : ℕ) (u : ℝ^n) :
    (p u)[i]? = if h : i < p.dim then .some ((p.val u)[⟨i,h⟩]) else .none := by
  simp[getElem?_def]

theorem plot_tangentMapEq_dim {p q : Plot (Array X) n} {u}
  (h : tangentMap (X:=Array X) p u = tangentMap (X:=Array X) q u) :
  p.dim = q.dim := by
  cases' p with dim  p _
  cases' q with dim' q _
  simp_all[tangentMap,tsMap']
  rw[(p u).2]; rw[(q u).2]
  exact congrArg Array.size h.1

theorem plot_tangentMapEq {dim : Nat} {p q : ℝ^n → ArrayN X dim} {hp : ContDiff ℝ ⊤ p} {hq : ContDiff ℝ ⊤ q} {u}
    (h : tangentMap (X:=Array X) (ArrayPlot.mk dim p hp) u = tangentMap (X:=Array X) (ArrayPlot.mk dim q hq) u) :
    p u = q u ∧ fderiv ℝ p u = fderiv ℝ q u := by
  have h := congrArg (tsMapInv' ·) h
  simp [tangentMap] at h
  constructor
  · apply ArrayN.ext_data; exact h.1
  · exact h.2


variable [Diffeology X] [StandardDiffeology X]


----------------------------------------------------------------------------------------------------
-- Array.get? --------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[fun_prop]
theorem Array.get?.arg_a.DSmooth_rule (i : ℕ) : DSmooth (fun x : Array X => x[i]?) := by
  constructor
  existsi (fun n ⟨dim,p,_⟩ =>
            if h : i < dim then
              .some (mkVecPlot (fun u => (p u)[⟨i,h⟩]) (by fun_prop))
            else
              .none)
  intros dim u p; simp
  split_ifs <;> simp


@[simp]
theorem plotMap_get? (i : ℕ) (p : Plot (Array X) n) :
    (fun x : Array X => x[i]?) ∘ₚ p
    =
    if h : i < p.dim then
      .some (mkVecPlot (fun u => (p.val u)[⟨i,h⟩]) (by have := p.contDiff; fun_prop))
    else
      none := by
  apply plot_ext; intro u;
  split_ifs <;> simp_all


theorem Array.get?.arg_a.TSSmooth (i : ℕ) :
    TSSmooth (fun x : Array X => x[i]?) := by

  constructor
  case toDSmooth => fun_prop

  case plot_independence =>
    intro n ⟨dim,p,ph⟩ ⟨dim',q,qh⟩ u h
    have hdim : dim = dim' := plot_tangentMapEq_dim h
    subst hdim
    simp (disch:=fun_prop)
    split_ifs with hi
    · simp[tangentMap,tsMap']
      have := plot_tangentMapEq h
      fun_trans; simp_all
    · rfl
  case tangentMap_exp => sorry


----------------------------------------------------------------------------------------------------
-- Array.append ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

#check Array.append

@[simp]
theorem ArrayN.data_get_int (x : ArrayN α n) (i : ℕ) (hi : i < x.data.size) :
    x.data[i] = x[⟨i,by rw[x.2]; exact hi⟩] := by rfl

def ArrayN.append (as : ArrayN α n) (bs : ArrayN α m) : ArrayN α (n+m) := ⟨as.data ++ bs.data, by simp⟩

theorem ArrayN.append_spec (as : ArrayN α n) (bs : ArrayN α m) :
    as.append bs
    =
    ⊞ (i : Fin (n+m)) =>
      if h : i.1 < n then
        as[⟨i,h⟩]
      else
        let i : Fin m := ⟨i.1 - n, by omega⟩
        bs[i] := by
  ext i; simp[ArrayN.append,Array.getElem_append]


@[fun_prop]
theorem ArrayN.append.arg_asbs.IsContinuousLinearMap_rule
    {X : Type u_1} [inst : NormedAddCommGroup X] [inst_1 : NormedSpace ℝ X] :
    IsContinuousLinearMap ℝ (fun ab : ArrayN X n × ArrayN X m => ab.1.append ab.2) := by
  simp[ArrayN.append_spec]; fun_prop


omit [Diffeology X] [StandardDiffeology X] in
@[fun_prop]
theorem _root_.Array.append.arg_asbs.DSmooth_rule : DSmooth (fun x : Array X×Array X => x.1 ++ x.2) := by
  constructor
  existsi (fun n (⟨dim,p,_⟩,⟨dim',q,_⟩) =>
            ⟨dim+dim', fun u => (p u).append (q u), by fun_prop⟩)
  intros dim u p; simp
  ext i; simp;
  cases p
  simp[ArrayN.append,Array.getElem_append]; rfl


omit [Diffeology X] [StandardDiffeology X] in
@[simp]
theorem plotMap_append (p : Plot (Array X × Array X) n) :
  (fun x : Array X×Array X => x.1 ++ x.2) ∘ₚ p
  =
  ⟨p.1.dim + p.2.dim, fun u => (p.1.val u).append (p.2.val u), by fun_prop⟩ := by
  cases p; ext u <;> simp; rfl


@[fun_prop]
theorem ContDiff.differentiableAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (hf : ContDiff ℝ ⊤ f) (x : X) : DifferentiableAt ℝ f x := by
  fun_prop (config:={maxTransitionDepth:=5})


omit [Diffeology X] [StandardDiffeology X] in
@[fun_prop]
theorem _root_.Array.append.arg_asbs.TSSmooth_rule : TSSmooth (fun x : Array X×Array X => x.1 ++ x.2) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u
    intro h
    have h : tmTranspose'.symm (tangentMap p u) = tmTranspose'.symm (tangentMap q u) := by rw[h]
    simp at h
    have hdim  := plot_tangentMapEq_dim h.1
    have hdim' := plot_tangentMapEq_dim h.2
    cases' p with p p'; cases p; cases p'
    cases' q with q q'; cases q; cases q'
    simp_all
    subst hdim; subst hdim'
    have hp1 := plot_tangentMapEq h.1
    have hp2 := plot_tangentMapEq h.2
    simp[tangentMap]
    apply tsMap'_ext
    · simp_all
    · fun_trans; simp_all
  case tangentMap_exp => sorry



----------------------------------------------------------------------------------------------------
-- Array.append ------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------



@[fun_prop]
theorem _root_.Array.setD.arg_av.DSmooth_rule (i : ℕ) :
    DSmooth (fun x : Array X×X => x.1.setD i x.2) := by

  constructor
  existsi (fun n (⟨dim,p,hp⟩,q) =>
    if hi : i < dim then
      ⟨dim, fun u => ArrayType.set (p u) ⟨i,hi⟩ (q u), by fun_prop⟩
    else
      ⟨dim,p,hp⟩)
  sorry


@[simp]
theorem plotMap_setD (i : ℕ) (p : Plot (Array X × X) n) :
    (fun x : Array X×X => x.1.setD i x.2) ∘ₚ p
    =
    if hi : i < p.1.dim then
      ⟨p.1.dim, fun u => ArrayType.set (p.1.val u) ⟨i,hi⟩ (p.2 u), by sorry⟩
    else
      p.1 := by
  sorry


@[fun_prop]
theorem _root_.Array.setD.arg_av.TSSmooth_rule (i : ℕ) :
    TSSmooth (fun x : Array X×X => x.1.setD i x.2) := by

  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u
    intro h
    have h : tmTranspose'.symm (tangentMap p u) = tmTranspose'.symm (tangentMap q u) := by rw[h]
    simp at h
    have hdim  := plot_tangentMapEq_dim h.1
    cases' p with p p'; cases' p with dim p hp
    cases' q with q q'; cases' q with dim' q hq
    simp_all
    subst hdim
    have hp1 := plot_tangentMapEq h.1
    have hp2 := h.2
    have hp2x : p' u = q' u := sorry
    have hp2dx : fderiv ℝ p' u = fderiv ℝ q' u := sorry
    by_cases hn : i < dim
    · simp only [hn,reduceDIte]
      simp only [tangentMap]
      apply tsMap'_ext
      simp only [hp2x,hp2dx,hp1.1,hp1.2]
      fun_trans only [hp2x,hp2dx,hp1.1,hp1.2]
    · simp only [hn,reduceDIte]
      exact h.1
  case tangentMap_exp => sorry
