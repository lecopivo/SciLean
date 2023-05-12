import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Solver.Solver 
import SciLean.Data.IdxProperties

open SciLean

variable {n : USize} [Nonempty (Idx n)]

-- set_option trace.Meta.synthInstance true in
def H (m k : ℝ) (x p : ℝ^{n}) : ℝ := 
  let Δx := (1 : ℝ)/(n : ℝ)
  (Δx/(2*m)) * ‖p‖² + (Δx * k/2) * (∑ i, ‖x[i.shiftPos 1] - x[i]‖²)

-- set_option trace.Meta.Tactic.lsimp.pre true in
-- set_option trace.Meta.Tactic.lsimp.post true in
function_properties H {n : USize} [Nonempty (Idx n)] (m k : ℝ) (x p : ℝ^{n}) : ℝ
argument x
  def ∂† by 
    unfold H
    fun_trans; fun_trans
argument p
  def ∂† by
    unfold H
    fun_trans; fun_trans


approx solver (m k : ℝ) (steps : Nat)
  :=  odeSolve (λ t (x,p) => ( ∇ (p':=p), H (n:=n) m k x p',
                              -∇ (x':=x), H (n:=n) m k x' p))

by
  -- Unfold Hamiltonian definition and compute gradients
  unfold gradient
  fun_trans

  -- Apply RK4 method
  rw [odeSolve_fixed_dt runge_kutta4_step]
  approx_limit steps; simp; intro steps'


def main : IO Unit := do

  let substeps := 1
  let m := 1.0
  let k := 10000.0

  let N : USize := 100
  have h : Nonempty (Idx N) := sorry

  let Δt := 0.1
  let x₀ : (ℝ^{N}) := ⊞ (i : Idx N), (Real.sin ((i.1 : ℝ)/10))
  let p₀ : (ℝ^{N}) := ⊞ i, (0 : ℝ)
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for i in [0:1000] do
  
    (x, p) := solver m k substeps t (x, p) (t+Δt)
    t += Δt

    let M : USize := 20
    for m in fullRange (Idx M) do
      for n in fullRange (Idx N) do
        let xi := x[n]
        if (2*m.1 - M)/(M : ℝ) - xi < 0  then
          IO.print "x"
        else
          IO.print "."

      IO.println ""


-- #eval main
