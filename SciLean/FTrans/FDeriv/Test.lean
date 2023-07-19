import SciLean.FTrans.FDeriv.Basic
import SciLean.Profile

open SciLean


variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

#profile_this_file

example 
  : fderiv K (fun (x : K) => x + x)
    =
    0 := 
by 
  ext x; simp
  ftrans only
  sorry

example 
  : fderiv K (fun (x : K) => x + x + x)
    =
    0 := 
by 
  ext x; simp
  ftrans only
  sorry

example 
  : fderiv K (fun (x : K) => x + x + x + x)
    =
    0 := 
by 
  ext x; simp
  ftrans only
  sorry

example 
  : fderiv K (fun (x : K) => x + x + x + x + x)
    =
    0 := 
by 
  ext x; simp
  ftrans only
  sorry

