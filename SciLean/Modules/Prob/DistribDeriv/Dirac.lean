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


-- @[fprop]
theorem dirac.differentiableAt (f : X → Y) (φ : Y → ℝ) (x : X) 
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) :
    DifferentiableAt ℝ (fun x => dirac (f x) φ) x := by dsimp[dirac]; fprop


-- @[fprop]
theorem dirac.bind._arg_xf.differentiableAt (g : X → Y) (f : X → Y → Distribution Z) (φ : Z → ℝ) (x : X) 
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x))  :
    DifferentiableAt ℝ (fun x => (dirac (g x)).bind (f x) φ) x := by dsimp[dirac]; fprop



@[simp]
theorem dirac.distribDeriv_comp (f : X → Y) (x dx : X) (φ : Y → ℝ)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    distribDeriv (fun x : X => dirac (f x)) x dx φ 
    =
    let y := f x
    let dy := fderiv ℝ f x dx
    fderiv ℝ φ y dy := by

  conv => 
    lhs 
    unfold distribDeriv dirac; dsimp
    ftrans; dsimp

  
@[simp]
theorem dirac.bind.arg_xf.distribDeriv_rule 
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → ℝ) 
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x)) :
    distribDeriv (fun x' => (dirac (g x')).bind (f x')) x dx φ
    =
    let y := g x
    let dy := fderiv ℝ g x dx
    (diracDeriv y dy).bind (f x ·) φ
    +
    distribDeriv (f · y) x dx φ := by

  simp [distribDeriv, dirac, diracDeriv, Distribution.bind]
  ftrans; dsimp
  rw[fderiv_uncurry (fun x y => f x y φ) (x, g x) _ hf]
  simp only [add_comm]


@[simp]
theorem dirac.distribFwdDeriv_comp (f : X → Y) (x dx : X) (φ : Y → ℝ)
    (hg : DifferentiableAt ℝ f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    distribFwdDeriv (fun x : X => dirac (f x)) x dx φ 
    =
    let ydy := fwdFDeriv ℝ f x dx
    fwdFDeriv ℝ φ ydy.1 ydy.2 := by

  unfold distribFwdDeriv
  simp (disch := assumption) only [FDistribution_apply, distribDeriv_comp]
  rfl
  

  
@[simp]
theorem dirac.bind.arg_xf.distribFwdDeriv_rule 
    (g : X → Y) (f : X → Y → Distribution Z) (x dx) (φ : Z → ℝ) 
    (hg : DifferentiableAt ℝ g x) (hf : DifferentiableAt ℝ (fun (x,y) => f x y φ) (x, g x)) :
    distribFwdDeriv (fun x' => (dirac (g x')).bind (f x')) x dx φ
    =
    let ydy := fwdFDeriv ℝ g x dx
    distribFwdDeriv (fun (x,y) => f x y) (x,ydy.1) (dx,ydy.2) φ := by

  unfold distribFwdDeriv distribDeriv; 
  simp only [dirac_bind, FDistribution_apply, Prod.mk.injEq]
  ftrans; 
  simp only [fwdFDeriv, ContinuousLinearMap.mk'_eval, and_self]
  
  

