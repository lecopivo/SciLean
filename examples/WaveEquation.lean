import SciLean

open SciLean

set_default_scalar Float

variable {n : Nat}

def _root_.SciLean.Idx.shift (i : Idx n) (j : USize) : Idx n := ⟨(i.1+j)%n, sorry_proof⟩

def H (m k : Float) (x p : Float^[n]) : Float :=
  let Δx := 1.0/n.toFloat
  (Δx/(2*m)) * ‖p‖₂² + (Δx * k/2) * (∑ᴵ i, ‖x[i.shift 1] - x[i]‖₂²)

/-!
This file used to showcase SciLean's `approx solver` pipeline.

At the moment, the full symbolic autodiff / `∂` transformation used here is
unstable across Mathlib/SciLean updates and can break the build.

To keep this example executable (and CI-friendly), we provide a small,
*computable* RK4 integrator with a hand-derived gradient for the Hamiltonian.
-/

def vec_add (x y : Float^[n]) : Float^[n] :=
  ⊞ i => x[i] + y[i]

def vec_scale (a : Float) (x : Float^[n]) : Float^[n] :=
  ⊞ i => a * x[i]

def vec_addScaled (x dx : Float^[n]) (a : Float) : Float^[n] :=
  ⊞ i => x[i] + a * dx[i]

def state_add (s₁ s₂ : Float^[n] × Float^[n]) : Float^[n] × Float^[n] :=
  (vec_add s₁.1 s₂.1, vec_add s₁.2 s₂.2)

def state_scale (a : Float) (s : Float^[n] × Float^[n]) : Float^[n] × Float^[n] :=
  (vec_scale a s.1, vec_scale a s.2)

def state_addScaled (s ds : Float^[n] × Float^[n]) (a : Float) : Float^[n] × Float^[n] :=
  (vec_addScaled s.1 ds.1 a, vec_addScaled s.2 ds.2 a)

def waveDeriv (m k : Float) (x p : Float^[n]) : (Float^[n] × Float^[n]) :=
  let Δx := 1.0 / n.toFloat
  let dx : Float^[n] := ⊞ i => (Δx / m) * p[i]
  let dp : Float^[n] := ⊞ i =>
    -- discrete Laplacian with periodic boundary conditions
    let iPrev := i.shift (USize.ofNat (n-1))
    let iNext := i.shift 1
    (Δx * k) * (x[iPrev] + x[iNext] - 2.0 * x[i])
  (dx, dp)

def rk4Step (m k : Float) (dt : Float) (s : Float^[n] × Float^[n]) : Float^[n] × Float^[n] :=
  let (x, p) := s
  let k1 := waveDeriv (n:=n) m k x p
  let k2 := waveDeriv (n:=n) m k (vec_addScaled x k1.1 (dt/2.0)) (vec_addScaled p k1.2 (dt/2.0))
  let k3 := waveDeriv (n:=n) m k (vec_addScaled x k2.1 (dt/2.0)) (vec_addScaled p k2.2 (dt/2.0))
  let k4 := waveDeriv (n:=n) m k (vec_addScaled x k3.1 dt) (vec_addScaled p k3.2 dt)

  let dx :=
    state_add
      (state_add k1 (state_scale 2.0 k2))
      (state_add (state_scale 2.0 k3) k4)
  state_addScaled s dx (dt/6.0)

def solver (m k : Float) (substeps : Nat) (t₀ t₁ : Float) (s : Float^[n] × Float^[n]) : Float^[n] × Float^[n] :=
  if substeps = 0 then
    s
  else
    Id.run do
      let dt := (t₁ - t₀) / substeps.toFloat
      let mut s := s
      for _ in [0:substeps] do
        s := rk4Step (n:=n) m k dt s
      return s



def main : IO Unit := do

  let substeps := 1
  let mass := 1.0
  let stiffness := 40000.0

  let N : Nat := 100

  let Δt := 0.1
  let x₀ : Float^[N] := ⊞ (i : Idx N) => (Scalar.sin (i.1.toNat.toFloat/10))
  let p₀ : Float^[N] := ⊞ (_ : Idx N) => (0 : Float)
  let mut t := 0
  let mut (x,p) := (x₀, p₀)

  for _ in [0:100] do

    (x,p) := solver (n:=N) mass stiffness substeps t (t+Δt) (x, p)
    t += Δt

    let height : Nat := 20
    for row in fullRange (Idx height) do
      for col in fullRange (Idx N) do
        let xi := x[col]
        if (2.0*row.1.toNat.toFloat - height.toFloat)/(height.toFloat) - xi < 0 then
          IO.print "x"
        else
          IO.print "."

      IO.println ""
