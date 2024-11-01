import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.NormedSpace

namespace SciLean


variable
  {X : Type*} {TX : outParam (X → Type*)} [Diffeology X]
  [∀ x, AddCommGroup (TX x)] [∀ x, Module ℝ (TX x)] [TangentSpace X TX]
  {Y : Type*} {TY : outParam (Y → Type*)} [Diffeology Y]
  [∀ y, AddCommGroup (TY y)] [∀ y, Module ℝ (TY y)] [TangentSpace Y TY]
  {Z : Type*} {TZ : outParam (Z → Type*)} [Diffeology Z]
  [∀ z, AddCommGroup (TZ z)] [∀ z, Module ℝ (TZ z)] [TangentSpace Z TZ]


variable (X Y)
@[ext]
structure DiffeologyMap where
  val : X → Y
  property : MDifferentiable val
variable {X Y}

instance : DFunLike (DiffeologyMap X Y) X (fun _ => Y) where
  coe f := f.1
  coe_injective' := by intro x y; aesop

@[simp]
theorem DiffeologyMap.beta (f : X → Y) (hf : MDifferentiable f) (x : X) :
   DiffeologyMap.mk f hf x = f x := by rfl

@[simp]
theorem DiffeologyMap.eta (f : DiffeologyMap X Y) :
   DiffeologyMap.mk f f.2 = f := by rfl

theorem DiffeologyMap.mem_plots (f : DiffeologyMap (Fin n → ℝ) X) :
    (fun x => f x) ∈ Diffeology.plots n := by

  apply f.2.plot_preserving (fun x => x)
  apply differentiable_id


open Diffeology Util in
instance : Diffeology (DiffeologyMap X Y) where
  plots := fun n p => ∀ m, ∀ q ∈ plots m (X:=X),
    (fun x : Fin (n + m) → ℝ => (p (FinAdd.fst x)) (q (FinAdd.snd x))) ∈ plots (n+m)
  smooth_comp := by
    intros n m p f hp hf
    intros m' q hq
    let f' : (Fin (n + m') → ℝ) → (Fin (m + m') → ℝ) :=
      fun x => FinAdd.mk (f (FinAdd.fst x)) (FinAdd.snd x)
    have hf' : Differentiable ℝ f' := by
      simp (config:={unfoldPartialApp:=true}) [f']; fun_prop
    have hp' := Diffeology.smooth_comp (hp m' q hq) hf'
    simp [Function.comp_def,f'] at hp'
    exact hp'
  const_plot := by
    intros n f m p hp
    exact smooth_comp (n:=n+m) (f:=FinAdd.snd) (f.2.plot_preserving _ hp) (by unfold FinAdd.snd; fun_prop)
