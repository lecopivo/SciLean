import SciLean
import SciLean.Profile

open SciLean

-- #profile_this_file

set_option profiler true

variable {K : Type _} [NontriviallyNormedField K]

variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]

variable {ι : Type _} [Fintype ι]

variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]
-- #profile_this_file


example 
  : cderiv K (fun (x : K) => x * x * x * x) 
    =
    0
:= by 
  ftrans only
  dsimp (config := {zeta := false})
  dsimp (config := {zeta := false})
  

#exit

-- set_option trace.Meta.Tactic.fprop.cache true
example (x' : K)
  : cderiv K (fun (x : K) => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x) x'
    =
    fun dx =>
      dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx  + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx  + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx
 := 
by 
  ftrans only

#check Nat

example :
  Differentiable K (fun (x : K) => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x  + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x  + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x)
:= by fprop
