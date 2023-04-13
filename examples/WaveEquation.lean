import SciLean
import SciLean.Functions.OdeSolve
import SciLean.Solver.Solver 

open SciLean

variable {n : Nat} [Nonempty (Fin n)]

-- set_option trace.Meta.synthInstance true in
def H (m k : ℝ) (x p : ℝ^{n}) : ℝ := 
  let Δx := (1 : ℝ)/(n : ℝ)
  (Δx/(2*m)) * ‖p‖² + (Δx * k/2) * (∑ i , ‖x[i.shift 1] - x[i]‖²)


function_properties H {n : Nat} [Nonempty (Fin n)] (m k : ℝ) (x p : ℝ^{n}) : ℝ
argument x
  def ∂† by 
    unfold H
    fun_trans; fun_trans; fun_trans
argument p
  def ∂† by
    unfold H
    fun_trans; fun_trans; fun_trans


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
  let k := 100000.0

  let N : Nat := 100
  have h : Nonempty (Fin N) := sorry

  let Δt := 0.1
  let x₀ : (ℝ^{N}) := ⊞ (i : Fin N), (Real.sin ((i.1 : ℝ)/10))
  let p₀ : (ℝ^{N}) := ⊞ i, (0 : ℝ)
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for i in [0:1000] do
  
    (x, p) := solver m k substeps t (x, p) Δt
    t += Δt

    let M : Nat := 20
    for (m : Nat) in [0:M] do
      for (n : Nat) in [0:N] do
        let n : Fin N := ⟨n, sorry⟩
        let xi := x[n]
        if (2*m - M)/(M : ℝ) - xi < 0  then
          IO.print "x"
        else
          IO.print "."

      IO.println ""


-- #eval main
