import SciLean.Data.DataArray
import SciLean.Numerics.Optimization.Optimjl.Utilities.Types
import SciLean.Numerics.Optimization.Optimjl.LinerSearches.Types
import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Calculus.Notation.FwdDeriv

namespace SciLean.Optimjl


variable {R} [RealScalar R]
set_default_scalar R

variable (R)
structure BackTracking where
    c_1 : R := 1e-4
    ρ_hi : R := 0.5
    ρ_lo : R := 0.1
    iterations : ℕ := 1000
    order : ℕ := 3
    maxstep : Option R := none
variable {R}

-- cache::Union{Nothing,LineSearchCache{TF}} = nothing


namespace BackTracking

variable [ToString R]

local instance [Zero R] : Inhabited R := ⟨0⟩

def call (ϕ : R → R) (ϕ₀ dϕ₀ x₀ : R) : LineSearchM (BackTracking R) Unit (R×R) := do
  let ⟨c₁, ρ_hi, ρ_lo, iterations, order, _⟩ ← read

  -- emptycache!(cache)
  -- pushcache!(cache, 0, ϕ₀, dϕ₀)  # backtracking doesn't use the slope except here

  assert! (order = 2 || order = 3)

  let mut iteration := 0

  let mut ϕx₀ := ϕ₀
  let mut ϕx₁ := ϕ₀

  let mut x₁ := x₀
  let mut x₂ := x₀

  ϕx₁ := ϕ x₁

  -- Hard-coded backtrack until we find a finite function value
  -- let iterfinitemax : R := sorry -- -log2(eps(real(Tx)))
  -- iterfinite = 0
  -- while !isfinite(ϕx₁) && iterfinite < iterfinitemax
  --     iterfinite += 1
  --     x₁ = x₂
  --     x₂ = x₁/2

  --     ϕx₁ = ϕ(x₂)
  --   end
  --   pushcache!(cache, xinitial, ϕx₁)
  -- dbg_trace s!"  iteration\tαₙ\tf(x+αₙ•sₙ)"
  -- dbg_trace s!"  {iteration}\t{x₂}\t{ϕx₁}"

  -- Backtrack until we satisfy sufficient decrease condition
  while ϕx₁ > ϕ₀ + c₁ * x₂ * dϕ₀ do
    -- Increment the number of steps we've had to perform
    iteration += 1

    -- Ensure termination
    if iteration > iterations then
      panic! s!"Linesearch failed to converge, reached maximum iterations {iterations}." -- x₂

    let mut x_tmp : R := 0
    -- Shrink proposed step-size:
    if order == 2 || iteration == 1 then
      -- backtracking via quadratic interpolation:
      -- This interpolates the available data
      --    f(0), f'(0), f(x)
      -- with a quadractic which is then minimised; this comes with a
      -- guaranteed backtracking factor 0.5 * (1-c₁)^{-1} which is < 1
      -- provided that c₁ < 1/2; the backtrack_condition at the beginning
      -- of the function guarantees at least a backtracking factor ρ.
      x_tmp := - (dϕ₀ * x₂^2) / ( 2 * (ϕx₁ - ϕ₀ - dϕ₀*x₂) )
    else
      let div := (1:R) / (x₁^2 * x₂^2 * (x₂ - x₁))
      let a := (x₁^2*(ϕx₁ - ϕ₀ - dϕ₀*x₂) - x₂^2*(ϕx₀ - ϕ₀ - dϕ₀*x₁))*div
      let b := (-x₁^3*(ϕx₁ - ϕ₀ - dϕ₀*x₂) + x₂^3*(ϕx₀ - ϕ₀ - dϕ₀*x₁))*div

      if Scalar.abs (a) ≤ 1e-14 /- isapprox(a, zero(a), atol=eps(real(Tx))) -/ then
        x_tmp := dϕ₀ / (2*b)
      else
        -- discriminant
        let d := max (b^2 - 3*a*dϕ₀) 0
        -- quadratic equation root
        x_tmp := (-b + Scalar.sqrt d) / (3*a)

    x₁ := x₂

    x_tmp := min x_tmp (x₂*ρ_hi) -- avoid too small reductions
    x₂ := max x_tmp (x₂*ρ_lo) -- avoid too big reductions

    -- Evaluate f(x) at proposed position
    ϕx₀ := ϕx₁
    ϕx₁ := ϕ x₂

    -- dbg_trace s!"  {iteration}\t{x₂}\t{ϕx₁}"

    -- pushcache!(cache, x₂, ϕx₁)
  return (x₂, ϕx₁)


variable [ToString R]


instance : LineSearch0 R (BackTracking R) Unit where
  c₁ ls := ls.c_1
  summary ls verbose :=
    if ¬verbose then
       "Backtracking Line Search"
    else
       s!"Backtracking Line Search\
        \n  c₁ := {ls.c_1}\
        \n  ρ₁ := {ls.ρ_hi}\"
        \n  ρ₀ := {ls.ρ_lo}\
        \n  max iterations := {ls.iterations}\
        \n  order := {ls.order}\
        \n  max step := {if let some s := ls.maxstep then toString s else "∞"}"

  call φ φ₀ dφ₀ x₀ := call φ φ₀ dφ₀ x₀
