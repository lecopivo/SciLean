import SciLean.Analysis.Diffeology.Basic
import SciLean.Analysis.Diffeology.TangentSpace
import SciLean.Analysis.Diffeology.TangentBundle
import SciLean.Meta.SimpAttr
import SciLean.Analysis.Calculus.FwdFDeriv

namespace SciLean

variable
  {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y:Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

instance : Diffeology X where
  plots n f := ContDiff ℝ ⊤ f
  plot_comp := by
    intros; simp_all[Membership.mem,Set.Mem]; fun_prop
  const_plot := by
    intros; simp_all[Membership.mem,Set.Mem]; fun_prop


section TangentSpace
open TangentSpace

noncomputable
instance : TangentSpace X (fun _ => X) where
  tangentMap p _ u du := fderiv ℝ p u du
  tangentMap_comp := by
    intros n m p f hp hf t dt
    simp[Diffeology.plots,Membership.mem,Set.Mem] at hp
    simp_all[Membership.mem,Set.Mem,Function.comp_def]; fun_trans
  tangentMap_const := by intros; simp_all
  exp x dx t := x + t 0 • dx
  exp_at_zero := by simp
  exp_is_plot := by intros; simp_all[Membership.mem,Set.Mem,Diffeology.plots]; fun_prop
  tangentMap_exp_at_zero := by intros; fun_trans
  tangentMap_linear := by intros; constructor <;> simp

@[fun_prop]
theorem TSSmooth_differentiable (f : X → Y) (hf : ContDiff ℝ ⊤ f) : TSSmooth f where
  plot_preserving p hp := by
    simp[Function.comp_def]; have : ContDiff .. := hp
    dsimp[Diffeology.plots, Membership.mem,Set.Mem]
    fun_prop

  plot_independence {n p q} x hp hq hx hdx := by
    have : ContDiff .. := hp; have : ContDiff .. := hq
    simp_all [tangentMap,Function.comp_def]
    fun_trans; simp_all


@[simp, simp_core]
theorem tsderiv_fderiv (f : X → Y) (hf : ContDiff ℝ ⊤ f := by fun_prop) :
    tsderiv f = fun x dx => fderiv ℝ f x dx := by
  funext x dx
  have : TSSmooth f := by fun_prop
  unfold tsderiv; simp_all[tangentMap,exp,Function.comp_def]
  fun_trans

end TangentSpace


section TangentBundle
open TangentBundle

/-- Tangent bundle of vector space `X`, it is just `X×X` but equiped with non-standard instances. -/
@[ext]
structure VecTangentBundle (X : Type u) where
  fst : X
  snd : X

def VecTangentBundle.toProd : (xdx : VecTangentBundle X) → X×X
  | ⟨x,dx⟩ => (x,dx)

def VecTangentBundle.ofProd : (xdx : X×X) → VecTangentBundle X
  | (x,dx) => ⟨x,dx⟩

noncomputable
instance : TangentBundle X (VecTangentBundle X) where
  proj := fun ⟨x,_⟩ => x
  tip := fun x => ⟨x,0⟩
  smul := fun s ⟨x,dx⟩ => ⟨x,s•dx⟩
  one_smul := by
    intro ⟨x,dx⟩
    calc _ = ⟨x,(1:ℝ)•dx⟩ := by rfl
         _ = _ := by simp
  proj_tip := by simp
  proj_smul := by simp
  zero_smul := by
    intro ⟨x,dx⟩
    calc _ = ⟨x,(0:ℝ)•dx⟩ := by rfl
         _ = _ := by simp
  smul_zero := by
    intro s x
    calc _ = ⟨x,s•0⟩ := by rfl
         _ = _ := by simp
  smul_smul := by
    intro s r ⟨x,dx⟩
    calc _ = ⟨x,s•r•dx⟩ := by rfl
         _ = ⟨x,(s*r)•dx⟩ := by rw[smul_smul]
         _ = _ := by rfl
  mul_smul := by
    intro s r ⟨x,dx⟩
    calc _ = ⟨x,(s*r)•dx⟩ := by rfl
         _ = ⟨x,s•r•dx⟩ := by rw[←smul_smul]
         _ = _ := by rfl
  tangentMap p _ u du := ⟨p u, fderiv ℝ p u du⟩
  tangentMap_proj := by simp
  tangentMap_comp := by
    intro n m p hp f hf u du
    have : ContDiff .. := hp
    fun_trans [Function.comp_def]
  tangentMap_const := by simp
  tangentMap_smul := by
    intro n p hp u du s
    calc _ = ⟨p u, s• (fderiv ℝ p u) du⟩ := by rfl
         _ = _ := by simp
  exp := fun ⟨x,dx⟩ t => ⟨x+t 0•dx,dx⟩
  exp_at_zero := by intro ⟨x,dx⟩; simp
  exp_is_plot := by intro ⟨x,dx⟩; dsimp[Diffeology.plots, Membership.mem,Set.Mem]; fun_prop
  tangentMap_exp_at_zero := by
    intro ⟨x,dx⟩
    fun_trans
    rfl


@[fun_prop]
theorem TBSmooth_differentiable (f : X → Y) (hf : ContDiff ℝ ⊤ f) : TBSmooth f where
  plot_preserving p hp := by
    simp[Function.comp_def]; have : ContDiff .. := hp
    dsimp[Diffeology.plots, Membership.mem,Set.Mem]
    fun_prop

  plot_independence {n} p q x hp hq hx := by
    have : ContDiff .. := hp; have : ContDiff .. := hq
    simp_all [tangentMap,Function.comp_def]
    have h := fun du => congrArg VecTangentBundle.fst (congrFun hx du)
    have h' := fun du => congrArg VecTangentBundle.snd (congrFun hx du)
    simp at h h'
    fun_trans; simp_all


@[simp, simp_core]
theorem tbderiv_fderiv (f : X → Y) (hf : ContDiff ℝ ⊤ f := by fun_prop) :
    tbderiv f = fun xdx => VecTangentBundle.ofProd (fwdFDeriv ℝ f xdx.fst xdx.snd) := by
  funext ⟨x,dx⟩
  have : TBSmooth f := by fun_prop
  simp_all[tbderiv,tangentMap,exp,Function.comp_def,
           VecTangentBundle.ofProd,fwdFDeriv,FiberBundle.proj]
  fun_trans


end TangentBundle
