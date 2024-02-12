import SciLean.Modules.Prob.DistribDeriv.DistribDeriv
import SciLean.Modules.Prob.DistribDeriv.DistribFwdDeriv

namespace SciLean.Prob

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]


noncomputable
def diracDeriv (x dx : X) : Distribution X := fun φ => fderiv ℝ φ x dx

noncomputable
def diracFwdDeriv (x dx : X) : FDistribution X := { val := dirac x, dval := diracDeriv x dx }

-- @[fprop]
theorem dirac.differentiableAt (f : X → Y) (φ : Y → ℝ) (x : X)
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) :
    DifferentiableAt ℝ (fun x => dirac (f x) φ) x := by dsimp[dirac]; fprop


-- @[fprop]
theorem dirac.bind._arg_xf.differentiableAt (g : X → Y) (f : X → Y → Distribution Z) (φ : Z → ℝ) (x : X)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x))  :
    DifferentiableAt ℝ (fun x => bind (dirac (g x)) (f x) φ) x := by dsimp[bind,dirac]; fprop



@[simp]
theorem dirac.distribDeriv_comp (f : X → Y) (x dx : X) (φ : Y → ℝ)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    distribDeriv (fun x : X => dirac (f x)) x dx φ
    =
    let y := f x
    let dy := fderiv ℝ f x dx
    diracDeriv y dy φ  := by

  conv =>
    lhs
    unfold distribDeriv dirac; dsimp
    ftrans; dsimp


@[simp]
theorem dirac.bind.arg_xf.distribDeriv_rule
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → ℝ)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x)) :
    distribDeriv (fun x' => bind (dirac (g x')) (f x')) x dx φ
    =
    let y := g x
    let dy := fderiv ℝ g x dx
    bind (diracDeriv y dy) (f x ·) φ
    +
    distribDeriv (f · y) x dx φ := by

  simp [bind, distribDeriv, dirac, diracDeriv]
  ftrans; dsimp
  rw[fderiv_uncurry (fun x y => f x y φ) (x, g x) _ hf]
  simp only [add_comm]


@[simp]
theorem dirac.distribFwdDeriv_comp (f : X → Y) (x dx : X) (φ : Y → ℝ×ℝ)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    distribFwdDeriv (fun x : X => dirac (f x)) x dx φ
    =
    let ydy := fwdFDeriv ℝ f x dx
    diracFwdDeriv ydy.1 ydy.2 φ := by

  unfold distribFwdDeriv
  simp (disch:=first | assumption | fprop) [FDistribution_apply, distribDeriv_comp, diracFwdDeriv, fwdFDeriv]


@[simp]
theorem dirac.bind.arg_xf.distribFwdDeriv_rule
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → ℝ×ℝ)
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y (fun x => (φ x).1)) (x, g x)) :
    distribFwdDeriv (fun x' => bind (dirac (g x')) (f x')) x dx φ
    =
    let ydy := fwdFDeriv ℝ g x dx
    distribFwdDeriv (fun (x,y) => f x y) (x,ydy.1) (dx,ydy.2) φ := by

  unfold distribFwdDeriv;
  simp (disch := assumption) only [FDistribution_apply, distribDeriv_rule, Prod.mk.injEq]
  constructor
  . rfl
  . simp (disch := assumption) only [bind, diracDeriv, distribDeriv, dirac, fwdFDeriv, add_left_inj]
    rw[fderiv_uncurry (fun x y => f x y (fun x => (φ x).1)) _ _ hf]
    ring
