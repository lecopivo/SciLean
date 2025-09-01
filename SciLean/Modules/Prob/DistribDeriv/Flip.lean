import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv

namespace SciLean.Prob

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]


noncomputable
def flip (θ : ℝ) : Distribution Bool := ⟨fun φ => θ • φ true + (1-θ) • φ false⟩

def dflip (dθ : ℝ) : Distribution Bool := ⟨fun φ => dθ • φ true - (dθ • φ false)⟩

noncomputable
def fdflip (θ dθ : ℝ) : FDistribution Bool := ⟨flip θ, dflip dθ⟩


-- @[fprop]
theorem flip.differentiableAt (f : X → ℝ) (φ : Bool → W) (x : X)
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun x => ⟪flip (f x), φ⟫) x := by dsimp[flip,action]; fprop


-- @[fprop]
theorem flip.bind._arg_xf.differentiableAt (g : X → ℝ) (f : X → Bool → Distribution Z) (φ : Z → W) (x : X)
    (hg : DifferentiableAt ℝ g x) (hf : ∀ b, DifferentiableAt ℝ (fun x => ⟪f x b, φ⟫) x)  :
    DifferentiableAt ℝ (fun x => ⟪(flip (g x)) >>= (f x), φ⟫) x := by

  dsimp only [bind,pure,fdaction_unfold,flip,fdaction_mk_apply,action]; simp
  fprop


@[simp ↓]
theorem flip.distribDeriv_comp (f : X → ℝ) (x dx : X) (φ : Bool → W)
    (hg : DifferentiableAt ℝ f x) :
    ⟪distribDeriv (fun x : X => flip (f x)) x dx, φ⟫
    =
    let dy := fderiv ℝ f x dx
    ⟪dflip dy, φ⟫  := by

  unfold distribDeriv flip dflip; simp only [action]
  ftrans
  simp only [ContinuousLinearMap.mk'_eval, neg_smul, sub_eq_add_neg]


@[simp ↓]
theorem flip.bind.arg_xf.distribDeriv_rule
    (g : X → ℝ) (f : X → Bool → Distribution Z) (x dx) (φ : Z → W)
    (hg : DifferentiableAt ℝ g x) (hf : ∀ b, DifferentiableAt ℝ (fun x => ⟪f x b, φ⟫) x) :
    ⟪distribDeriv (fun x' => bind (flip (g x')) (f x')) x dx, φ⟫
    =
    let y := g x
    let dy := fderiv ℝ g x dx
    ⟪dflip dy >>= (f x ·), φ⟫
    +
    ⟪flip y, fun y => ⟪distribDeriv (f · y) x dx, φ⟫⟫ := by

  simp only [bind, distribDeriv, flip, dflip,action]; simp only [distribution_action_normalize]
  ftrans;
  simp only [distribution_action_normalize, ContinuousLinearMap.mk'_eval, sub_eq_add_neg, neg_smul]
  abel



@[simp ↓]
theorem flip.distribFwdDeriv_comp (f : X → ℝ) (x dx : X) (φ : Bool → W×W)
    (hg : DifferentiableAt ℝ f x) :
    ⟪distribFwdDeriv (fun x : X => flip (f x)) x dx, φ⟫
    =
    let ydy := fwdFDeriv ℝ f x dx
    ⟪fdflip ydy.1 ydy.2, φ⟫ := by

  unfold distribFwdDeriv fdflip
  simp (disch := assumption) only [fdaction_mk_apply, distribDeriv_comp,fwdFDeriv]



@[simp ↓]
theorem flip.bind.arg_xf.distribFwdDeriv_rule
    (g : X → ℝ) (f : X → Bool → Distribution Z) (x dx) (φ : Z → W×W)
    (hg : DifferentiableAt ℝ g x) (hf : ∀ b, DifferentiableAt ℝ (fun x => ⟪f x b, fun x => (φ x).1⟫) x) :
    ⟪distribFwdDeriv (fun x' => bind (flip (g x')) (f x')) x dx, φ⟫
    =
    let ydy := fwdFDeriv ℝ g x dx
    ⟪fdflip ydy.1 ydy.2, fun y => ⟪distribFwdDeriv (f · y) x dx, φ⟫⟫ := by

  unfold distribFwdDeriv fdflip
  simp (disch := assumption) [fdaction_mk_apply, distribDeriv_rule, Pi.smul_apply, smul_eq_mul,  Prod.mk.injEq]
  simp (disch := assumption) [bind, flip, smul_eq_mul, fwdFDeriv, Pi.smul_apply, true_and,sub_eq_add_neg,action,distribDeriv]
  sorry
