import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv

namespace SciLean.Prob

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]


noncomputable
def pureDeriv (x dx : X) : Distribution X := fun φ => fderiv ℝ φ x dx

noncomputable
def pureFwdDeriv (x dx : X) : FDistribution X := { val := pure x, dval := pureDeriv x dx }

-- @[fprop]
theorem pure.differentiableAt (f : X → Y) (φ : Y → ℝ) (x : X)
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) :
    DifferentiableAt ℝ (fun x => pure (f:=Distribution) (f x) φ) x := by dsimp[pure]; fprop


-- @[fprop]
theorem pure.bind._arg_xf.differentiableAt (g : X → Y) (f : X → Y → Distribution Z) (φ : Z → ℝ) (x : X)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x))  :
    DifferentiableAt ℝ (fun x => bind (pure (g x)) (f x) φ) x := by dsimp[bind,pure]; fprop



@[simp]
theorem pure.distribDeriv_comp (f : X → Y) (x dx : X) (φ : Y → ℝ)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    distribDeriv (fun x : X => pure (f x)) x dx φ
    =
    let y := f x
    let dy := fderiv ℝ f x dx
    pureDeriv y dy φ  := by

  conv =>
    lhs
    unfold distribDeriv; dsimp[pure]
    ftrans; dsimp


@[simp]
theorem pure.bind.arg_xf.distribDeriv_rule
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → ℝ)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x)) :
    distribDeriv (fun x' => bind (pure (g x')) (f x')) x dx φ
    =
    let y := g x
    let dy := fderiv ℝ g x dx
    bind (pureDeriv y dy) (f x ·) φ
    +
    distribDeriv (f · y) x dx φ := by

  simp [bind, distribDeriv, pure, pureDeriv]
  ftrans; dsimp
  rw[fderiv_uncurry (fun x y => f x y φ) (x, g x) _ hf]
  simp only [add_comm]


@[simp]
theorem pure.distribFwdDeriv_comp (f : X → Y) (x dx : X) (φ : Y → ℝ×ℝ)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    distribFwdDeriv (fun x : X => pure (f x)) x dx φ
    =
    let ydy := fwdFDeriv ℝ f x dx
    pureFwdDeriv ydy.1 ydy.2 φ := by

  unfold distribFwdDeriv
  simp (disch:=first | assumption | fprop) [FDistribution_apply, distribDeriv_comp, pureFwdDeriv, fwdFDeriv]


@[simp]
theorem pure.bind.arg_xf.distribFwdDeriv_rule
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → ℝ×ℝ)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y (fun x => (φ x).1)) (x, g x)) :
    distribFwdDeriv (fun x' => bind (pure (g x')) (f x')) x dx φ
    =
    let ydy := fwdFDeriv ℝ g x dx
    distribFwdDeriv (fun (x,y) => f x y) (x,ydy.1) (dx,ydy.2) φ := by

  unfold distribFwdDeriv;
  simp (disch := assumption) only [FDistribution_apply, distribDeriv_rule, Prod.mk.injEq]
  constructor
  . rfl
  . simp (disch := assumption) only [bind, pureDeriv, distribDeriv, pure, fwdFDeriv, add_left_inj]
    rw[fderiv_uncurry (fun x y => f x y (fun x => (φ x).1)) _ _ hf]
    ring
