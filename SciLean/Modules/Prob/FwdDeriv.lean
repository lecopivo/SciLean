import Mathlib.Analysis.Calculus.FDeriv.Basic
import Probly.SimpAttr


variable {K : Type*} [NontriviallyNormedField K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F]


variable (K)

noncomputable
def fwdDeriv (f : E → F) (x dx : E) : F×F := (f x, fderiv K f x dx)
variable {K}


@[simp,rand_AD]
theorem fwdDeriv_id : fwdDeriv K (fun x : E => x) = fun x dx => (x,dx) := sorry


@[simp,rand_AD]
theorem fwdDeriv_const (y : F) : fwdDeriv K (fun x : E => y) = fun x dx => (y,0) := sorry
