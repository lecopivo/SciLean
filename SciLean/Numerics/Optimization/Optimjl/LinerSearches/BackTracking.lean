import SciLean.Data.DataArray
import SciLean.Numerics.Optimization.Optimjl.Utilities.Types

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
    --cache::Union{Nothing,LineSearchCache{TF}} = nothing


namespace BackTracking


def call (ls : BackTracking R) (ϕ : R → R) /-(dϕ : R → R) (ϕdϕ : R → R×R)-/ (αinitial ϕ₀ dϕ₀ : R) : R×R := Id.run do
  let mut ⟨c₁, ρ_hi, ρ_lo, iterations, order, _⟩ := ls

  -- emptycache!(cache)
  -- pushcache!(cache, 0, ϕ₀, dϕ₀)  # backtracking doesn't use the slope except here

  assert! (order = 2 || order = 3)


  let mut iteration := 0

  let mut ϕx₀ := ϕ₀
  let mut ϕx₁ := ϕ₀

  let mut α₁ := αinitial
  let mut α₂ := αinitial

  ϕx₁ := ϕ α₁

  -- Hard-coded backtrack until we find a finite function value
  -- let iterfinitemax : R := sorry -- -log2(eps(real(Tα)))
  -- iterfinite = 0
  -- while !isfinite(ϕx₁) && iterfinite < iterfinitemax
  --     iterfinite += 1
  --     α₁ = α₂
  --     α₂ = α₁/2

  --     ϕx₁ = ϕ(α₂)
  --   end
  --   pushcache!(cache, αinitial, ϕx₁)

  -- Backtrack until we satisfy sufficient decrease condition
  while ϕx₁ > ϕ₀ + c₁ * α₂ * dϕ₀ do
    -- Increment the number of steps we've had to perform
    iteration += 1

    -- Ensure termination
    if iteration > iterations then
        panic! s!"Linesearch failed to converge, reached maximum iterations {iterations}." -- α₂

    let mut α_tmp : R := 0
    -- Shrink proposed step-size:
    if order == 2 || iteration == 1 then
        -- backtracking via quadratic interpolation:
        -- This interpolates the available data
        --    f(0), f'(0), f(α)
        -- with a quadractic which is then minimised; this comes with a
        -- guaranteed backtracking factor 0.5 * (1-c₁)^{-1} which is < 1
        -- provided that c₁ < 1/2; the backtrack_condition at the beginning
        -- of the function guarantees at least a backtracking factor ρ.
        α_tmp := - (dϕ₀ * α₂^2) / ( 2 * (ϕx₁ - ϕ₀ - dϕ₀*α₂) )
    else
        let div := (1:R) / (α₁^2 * α₂^2 * (α₂ - α₁))
        let a := (α₁^2*(ϕx₁ - ϕ₀ - dϕ₀*α₂) - α₂^2*(ϕx₀ - ϕ₀ - dϕ₀*α₁))*div
        let b := (-α₁^3*(ϕx₁ - ϕ₀ - dϕ₀*α₂) + α₂^3*(ϕx₀ - ϕ₀ - dϕ₀*α₁))*div

        if true /- isapprox(a, zero(a), atol=eps(real(Tα))) -/ then
          α_tmp := dϕ₀ / (2*b)
        else
          -- discriminant
          let d := max (b^2 - 3*a*dϕ₀) 0
          -- quadratic equation root
          α_tmp := (-b + Scalar.sqrt d) / (3*a)

    α₁ := α₂

    α_tmp := min α_tmp (α₂*ρ_hi) -- avoid too small reductions
    α₂ := max α_tmp (α₂*ρ_lo) -- avoid too big reductions

    -- Evaluate f(x) at proposed position
    ϕx₀ := ϕx₁
    ϕx₁ := ϕ α₂
    -- pushcache!(cache, α₂, ϕx₁)
  return (α₂, ϕx₁)


variable {X} [NormedAddCommGroup X] [AdjointSpace R X]


def init (ls : BackTracking R) (d : ObjectiveFunction R X) (x s : X) (α₀ : R) (ϕ₀ dϕ₀ : Option R) (alphamax : R) : R×R :=
    let ϕ := fun α : R => d.f (x + α•s) -- make_ϕ_dϕ(df, x_new, x, s)

    let ϕ₀  := ϕ₀.getD (ϕ 0)
    let dϕ₀ := dϕ₀.getD ⟪(d.f' x).2 1, s⟫

    let alphamax := if let some ms := ls.maxstep then (min alphamax  (ms / ‖s‖₂)) else alphamax
    let α₀ := min α₀ alphamax
    (ls.call ϕ α₀ ϕ₀ dϕ₀)
