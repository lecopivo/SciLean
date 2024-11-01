import SciLean.Analysis.Diffeology.Basic

namespace SciLean

variable
  {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

instance : Diffeology X where
  plots n f := Differentiable ℝ f
  smooth_comp := by
    intros; simp_all[Membership.mem,Set.Mem]; fun_prop
  const_plot := by
    intros; simp_all[Membership.mem,Set.Mem]

noncomputable
instance : TangentSpace X (fun _ => X) where
  tangent c _ t dt := fderiv ℝ c t dt
  smooth_comp := by
    intros n m p f hp hf t dt
    simp[Diffeology.plots,Membership.mem,Set.Mem] at hp
    simp_all[Membership.mem,Set.Mem,Function.comp_def]; fun_trans
  tangent_const := by intros; simp_all
  curve x dx t := x + t 0 • dx
  curve_at_zero := by simp
  curve_is_plot := by intros; simp_all[Membership.mem,Set.Mem,Diffeology.plots]; fun_prop
  tangent_curve_at_zero := by intros; fun_trans
  tangent_linear := by intros; constructor <;> simp


set_option trace.Meta.Tactic.fun_trans true in
@[fun_prop]
theorem mdifferentiable_differentiable (f : X → Y) (hf : Differentiable ℝ f) : MDifferentiable f where
  plot_preserving p hp x := by
    simp[Function.comp_def]; have := hp x
    fun_prop

  plot_independence {n p q} x hp hq hx hdx := by
    have := hp x; have := hq x
    simp_all [TangentSpace.tangent,Function.comp_def]
    fun_trans; simp_all


@[simp, simp_core]
theorem mderiv_fderiv (f : X → Y) (hf : Differentiable ℝ f := by fun_prop) :
    mderiv f = fun x dx => fderiv ℝ f x dx := by
  funext x dx
  have : MDifferentiable f := by fun_prop;
  have := hf x
  unfold mderiv; simp_all[TangentSpace.tangent,TangentSpace.curve,Function.comp_def]
  fun_trans



variable
  {E : Type*} {TE : outParam (E → Type*)} [Diffeology E] [∀ e, AddCommGroup (TE e)] [∀ e, Module ℝ (TE e)] [TangentSpace E TE]

theorem aa (f : Y → E) (g : X → Y) (hf : MDifferentiable f) (hg : Differentiable ℝ g) :
  MDifferentiable (fun x => f (g x)) := by fun_prop

#print axioms aa
