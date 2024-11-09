import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.Prod
-- import SciLean.Analysis.Diffeology.SumInstances

namespace SciLean

local notation:max "ℝ^" n:max => Fin n → ℝ

open Diffeology

variable {X Y : Type*} [Diffeology X] [Diffeology Y]

open Diffeology in
instance : Diffeology (Sum X Y) where
  Plot n := Plot X n ⊕ Plot Y n
  plotEval p u := p.map (fun p => p u) (fun q => q u)
  plot_ext p q h :=
    match p, q with
    | .inl p, .inl q => by
      congr; ext x; simp at h
      have h := congrFun h x
      simp_all
    | .inr p, .inr q => by
      congr; ext x; simp at h
      have h := congrFun h x
      simp_all
    | .inl _, .inr _ => by have h := congrFun h 0; simp at h;
    | .inr _, .inl _ => by have h := congrFun h 0; simp at h;
  plotComp p f hf := p.map (fun p => plotComp p hf) (fun q => plotComp q hf)
  plotComp_eval := by
    intro n m p f hf u
    cases p <;> simp
  constPlot n x := x.map (fun x => constPlot n x) (fun y => constPlot n y)
  constPlot_eval := by
    intro n x? u
    cases x? <;> simp


@[simp]
theorem SumPlot.eval_inl' (f : Plot X n) :
    DFunLike.coe (F:=Plot (Sum X Y) n) (.inl f) = fun u => .inl (f u) := by rfl

@[simp]
theorem SumPlot.eval_inr' (f : Plot Y n) :
    DFunLike.coe (F:=Plot (Sum X Y) n) (.inr f) = fun u => .inr (f u) := by rfl


@[reducible]
instance {α : Type*} {β : α → Type u} {γ : Type*} {δ : γ → Type u}
         [∀ a, AddCommGroup (β a)] [∀ c, AddCommGroup (δ c)] (ac : α ⊕ γ) : AddCommGroup (Sum.rec β δ ac) :=
  match ac with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


@[reducible]
instance {α : Type*} {β : α → Type u} {γ : Type*} {δ : γ → Type u}
         [Semiring R]
         [∀ a, AddCommGroup (β a)] [∀ a, Module R (β a)] [∀ c, AddCommGroup (δ c)] [∀ c, Module R (δ c)] (ac : α ⊕ γ) :
         Module R (Sum.rec β δ ac) :=
  match ac with
  | .inl _ => by infer_instance
  | .inr _ => by infer_instance


def tsSumMap'
    {X : Type*} {TX : X → Type _} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)]
    {Y : Type*} {TY : Y → Type _} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)]
    {U : Type*} [AddCommGroup U] [Module ℝ U]:
    (Σ x, U →ₗ[ℝ] TX x) ⊕ (Σ y, U →ₗ[ℝ] TY y) ≃ Σ (xy : X⊕Y), (U →ₗ[ℝ] Sum.rec TX TY xy) where

  toFun := fun xdx => xdx.elim (fun ⟨x,dx⟩ => ⟨Sum.inl x, dx⟩) (fun ⟨y,dy⟩ => ⟨Sum.inr y, dy⟩)
  invFun := fun xdx =>
    match xdx with
    | ⟨.inl x, dx⟩ => .inl ⟨x,dx⟩
    | ⟨.inr y, dy⟩ => .inr ⟨y,dy⟩
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro ⟨x,dx⟩; cases x <;> simp

def tsSumMMap
    {X : Type*} {TX : X → Type _}
    {Y : Type*} {TY : Y → Type _} :
    (Σ x, TX x) ⊕ (Σ y, TY y) ≃ Σ (xy : X⊕Y), (Sum.rec TX TY xy) where

  toFun := fun xdx => xdx.elim (fun ⟨x,dx⟩ => ⟨Sum.inl x, dx⟩) (fun ⟨y,dy⟩ => ⟨Sum.inr y, dy⟩)
  invFun := fun xdx =>
    match xdx with
    | ⟨.inl x, dx⟩ => .inl ⟨x,dx⟩
    | ⟨.inr y, dy⟩ => .inr ⟨y,dy⟩
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro ⟨x,dx⟩; cases x <;> simp


open TangentSpace in
instance
    {X : Type u} {TX : outParam (X → Type v)} [Diffeology X]
    [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
    {Y : Type w} {TY : outParam (Y → Type v)} [Diffeology Y]
    [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY] :
    TangentSpace (Sum X Y) (Sum.rec TX TY) where

  tangentMap {n} p u := tsSumMap' (p.map (fun p => tangentMap p u) (fun q => tangentMap q u))
  exp := fun xdx => (tsSumMMap.symm xdx).map (fun xdx => exp xdx) (fun ydy => exp ydy)

  tangentMap_const := by intro n x u; cases x <;> simp[tsSumMap',constPlot]
  tangentMap_fst := by intro n x u; cases x <;> simp[tsSumMap']
  exp_at_zero := by intro ⟨x,dx⟩; cases x <;> simp[tsSumMMap]
  tangentMap_exp_at_zero := by intro ⟨x,dx⟩; cases x <;> simp[tsSumMMap,tsSumMap',duality]


variable
  {W : Type _} [Diffeology W] {TW : W → Type _} [∀ w, AddCommGroup (TW w)] [∀ w, Module ℝ (TW w)] [TangentSpace W TW]
  {X : Type _} [Diffeology X] {TX : X → Type _} [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type _} [Diffeology Y] {TY : Y → Type _} [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type _} [Diffeology Z] {TZ : Z → Type _} [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]

open TangentSpace

@[fun_prop]
theorem Sum.inl.arg_val.DSmooth_rule :
    DSmooth (@Sum.inl X Y) := by
  existsi fun _ p => .inl p
  intros; simp

@[simp]
theorem plotMap_inl (p : Plot X n) :
  (@Sum.inl X Y) ∘ₚ p = @Sum.inl (Plot X n) (Plot Y n) p := by ext u; simp

@[fun_prop]
theorem Sum.inl.arg_val.TSSmooth_rule :
    TSSmooth (@Sum.inl X Y) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u h
    simp_all[tangentMap]


@[fun_prop]
theorem Sum.inr.arg_val.DSmooth_rule :
    DSmooth (@Sum.inr X Y) := by
  existsi fun _ p => .inr p
  intros; simp

@[simp]
theorem plotMap_inr (p : Plot Y n) :
  (@Sum.inr X Y) ∘ₚ p = @Sum.inr (Plot X n) (Plot Y n) p := by ext u; simp

@[fun_prop]
theorem Sum.inr.arg_val.TSSmooth_rule :
    TSSmooth (@Sum.inr X Y) := by
  constructor
  case toDSmooth => fun_prop
  case plot_independence =>
    intro n p q u h
    simp_all[tangentMap]


@[fun_prop]
theorem Sum.elim.arg_fga0.DSmooth_rule
    (f : W → X → Z) (hf : DSmooth ↿f) (g : W → Y → Z) (hg : DSmooth ↿g)
    (a0 : W → X⊕Y) (ha0 : DSmooth a0) :
    DSmooth (fun w : W => Sum.elim (f w) (g w) (a0 w)) where
  ex_map_plot := by
    use (fun n p =>
             a0 ∘ₚ p |> Sum.map (fun p' => (p,p')) (fun p' => (p,p'))
                     |> Sum.elim (fun p => ↿f ∘ₚ p) (fun q => ↿g ∘ₚ q))
    intro n u p; simp
    have h : a0 (p u) = (a0 ∘[ha0] p) u := by simp
    rw[h];
    cases a0 ∘[ha0] p <;> (simp; rfl)


@[simp]
theorem plotMap_sum_elim (p : Plot W n)
    (f : W → X → Z) (hf : DSmooth ↿f) (g : W → Y → Z) (hg : DSmooth ↿g)
    (a0 : W → X⊕Y) (ha0 : DSmooth a0) :
    ((fun w : W => Sum.elim (f w) (g w) (a0 w)) ∘ₚ p)
    =
    (a0 ∘ₚ p |> Sum.map (fun p' => (p,p')) (fun p' => (p,p'))
             |> Sum.elim (fun p => ↿f ∘ₚ p) (fun q => ↿g ∘ₚ q)) := by

  ext u; simp
  have h : a0 (p u) = (a0 ∘[ha0] p) u := by simp
  rw[h]; cases (a0 ∘[ha0] p) <;> (simp; rfl)


@[fun_prop]
theorem Sum.elim.arg_fga0.TSSmooth_rule
    (f : W → X → Z) (hf : TSSmooth ↿f) (g : W → Y → Z) (hg : TSSmooth ↿g)
    (a0 : W → X⊕Y) (ha0 : TSSmooth a0) :
    TSSmooth (fun w : W => Sum.elim (f w) (g w) (a0 w)) where

  toDSmooth := by fun_prop
  plot_independence := by
    intro n p q u h
    simp (disch:=fun_prop)
    have hh := ha0.plot_independence h
    revert hh
    cases' a0∘ₚp with p' p'
    . cases' a0∘ₚq with q'
      · intro hh
        simp_all[tangentMap]
        have hh : tangentMap (p,p') u = tangentMap (X:=W×X) (q,q') u := by simp_all[tangentMap]
        exact hf.plot_independence hh
      · simp_all[tangentMap]
    . cases' a0∘ₚq with q' q'
      · simp_all[tangentMap]
      · intro hh
        simp_all[tangentMap]
        have hh : tangentMap (p,p') u = tangentMap (X:=W×Y) (q,q') u := by simp_all[tangentMap]
        exact hg.plot_independence hh
