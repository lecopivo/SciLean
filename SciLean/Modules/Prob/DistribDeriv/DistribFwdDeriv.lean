import SciLean.Core.FunctionTransformations
import SciLean.Modules.Prob.DistribDeriv.DistribDeriv

namespace SciLean.Prob


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]


structure FDistribution (X : Type _) where
  val  : Distribution X
  dval : Distribution X

instance : DistributionActionNotation (FDistribution X) (X → Y×Y) (Y×Y) where
  action := fun f φ => (⟪f.val, fun x => (φ x).1⟫, ⟪f.dval, fun x => (φ x).1⟫ + ⟪f.val, fun x => (φ x).2⟫)

@[simp]
theorem fdaction_mk_apply (val dval : Distribution X) (φ : X → W×W) :
    ⟪FDistribution.mk val dval, φ⟫ = (⟪val, fun x => (φ x).1⟫, ⟪dval, fun x => (φ x).1⟫ + ⟪val, fun x => (φ x).2⟫) := by rfl

theorem fdaction_unfold (f' : FDistribution X) (φ : X → W×W) :
    ⟪f', φ⟫ = (⟪f'.val, fun x => (φ x).1⟫, ⟪f'.dval, fun x => (φ x).1⟫ + ⟪f'.val, fun x => (φ x).2⟫) := by rfl

instance : Monad FDistribution where
  pure := fun x => { val := pure x, dval := 0 }
  bind := fun x f =>
    ⟨(x.val >>= (fun x' => (f x').val)),
     (x.dval >>= (fun x' => (f x').val))
     +
     (x.val >>= (fun x' => (f x').dval))⟩


----------------------------------------------------------------------------------------------------

noncomputable
def distribFwdDeriv
    (f : X → Distribution Y) (x dx : X) : FDistribution Y :=
  ⟨f x, distribDeriv f x dx⟩


@[simp]
theorem distribFwdDeriv_const (a : Distribution α) :
    distribFwdDeriv (fun _ : X => a)
    =
    fun w _dw => ⟨a,0⟩ := by unfold distribFwdDeriv; simp



-- WARNING: uses `distribDeriv_comp` axiom
theorem distribFwdDeriv_comp (f : Y → Distribution Z) (g : X → Y) (x dx : X) (φ : Z → W×W)
    (hf : DistribDifferentiable f) (hg : DifferentiableAt ℝ g x) :
    ⟪distribFwdDeriv (fun x : X => (f (g x))) x dx, φ⟫
    =
    let ydy := fwdFDeriv ℝ g x dx
    ⟪distribFwdDeriv f ydy.1 ydy.2, φ⟫ := by

  simp (disch := assumption) only [action, distribFwdDeriv, fwdFDeriv]
  simp (disch := assumption) only [distribution_action_normalize, distribDeriv_comp]



-- WARNING: uses `Rand.bind.arg_xf.distribDeriv_rule`
theorem FDistribution.bind.arg_xf.distribFwdDeriv_rule
    (g : X → Distribution Y) (f : X → Y → Distribution Z) (φ : Z → W×W) (x dx : X)
    (hg : DistribDifferentiable g) (hf : DistribDifferentiable (fun (x,y) => f x y)) :
    ⟪distribFwdDeriv (fun x' => Bind.bind (g x') (f x')) x dx, φ⟫
    =
    ⟪distribFwdDeriv g x dx, fun y => ⟪distribFwdDeriv (f · y) x dx, φ⟫⟫  := by

  simp (disch := assumption)
    [distribFwdDeriv, fdaction_mk_apply, action_bind,
     Bind.bind.arg_xf.distribDeriv_rule, Prod.mk.injEq, true_and, add_assoc]
  sorry -- linearity of ⟪g x, ·⟫




----------------------------------------------------------------------------------------------------


@[simp ↓]
theorem ite.arg_te.distribFwdDeriv_rule {c} [Decidable c] (t e : X → Distribution Y) (φ : Y → W×W) :
    ⟪distribFwdDeriv (fun x => if c then t x else e x) x dx, φ⟫
    =
    if c then ⟪distribFwdDeriv t x dx, φ⟫ else ⟪distribFwdDeriv e x dx, φ⟫ := by

  if h : c then simp[h] else simp[h]
