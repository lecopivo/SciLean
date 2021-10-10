import SciLean.Basic
import SciLean.Mechanics

set_option synthInstance.maxHeartbeats 50000
set_option synthInstance.maxSize 10000

def G : ℝ := 1.0

def T {n : Nat} (m : NDVector [n]) (v : NDVector [3, n]) : ℝ :=
do
  let mut energy : ℝ := 0
  for i in [0:n] do
    let mass := m.lget! i
    let vel  := (v.lget! (3*i), v.lget! (3*i+1), v.lget! (3*i+2)) -- this should be nicer
    energy := energy + mass/2 * ⟨vel, vel⟩
  energy


def V {n : Nat} (m : NDVector [n]) (x : NDVector [3, n]) : ℝ :=
do
  let mut energy : ℝ := 0 
  for i in [0:n] do
    let mi := m.lget! i
    let xi := (x.lget! (3*i), x.lget! (3*i+1), x.lget! (3*i+2))
    for j in [0:i] do
      let mj := m.lget! j
      let xj := (x.lget! (3*j), x.lget! (3*j+1), x.lget! (3*j+2)) 
      
      energy := energy + (G*mi*mj) / ∥xi - xj∥
  energy

def L {n} (m : NDVector [n]) (x v : NDVector [3, n]) := T m v - V m x

def solver {n} (m : NDVector [n]) (steps : Nat) : Impl (ode_solve (LagrangianSystem (L m))) := 
by  

  conv =>
    enter [1,1]
    whnf
    enter [xv]

  admit
  
  
  

  
