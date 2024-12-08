import SciLean.Data.DataArray
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Meta.Notation.Do

/-!

Port of Optim.jl

This is a port of: Optim.jl/src/multivariate/optimize/optimize.jl
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/multivariate/optimize/optimize.jl

-/

namespace SciLean.Optimjl

variable
  {R : Type} [RealScalar R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]


open Lean

variable (R X)
structure Method where
  isNewton : Bool
  isNewtonTrustRegion : Bool

structure ObjectiveFunction where
  f : X → R
  f' : X → R × (R → X)
  hf : HasRevFDeriv R f f'

structure Options where
  x_abstol : R := 0
  x_reltol : R := 0
  f_abstol : R := 0
  f_reltol : R := 0
  g_abstol : R := 1e-8
  g_reltol : R := 1e-8
  outer_x_abstol : R := 0
  outer_x_reltol : R := 0
  outer_f_abstol : R := 0
  outer_f_reltol : R := 0
  outer_g_abstol : R := 1e-8
  outer_g_reltol : R := 1e-8
  f_calls_limit : ℕ := 0
  g_calls_limit : ℕ := 0
  h_calls_limit : ℕ := 0
  allow_f_increases : Bool := true
  allow_outer_f_increases : Bool := true
  successive_f_tol : ℕ := 1
  iterations : ℕ := 1000
  outer_iterations : ℕ := 1000
  store_trace : Bool := false
  trace_simplex : Bool := false
  show_trace : Bool := false
  extended_trace : Bool := false
  show_warnings : Bool := true
  show_every: ℕ := 1
  callback : Unit → IO Unit := fun _ => pure ()
  time_limit? : Option ℕ := none

class AbstractOptimizerState (S : Type) where
  initialConvergence (d : ObjectiveFunction R X) (state : S) (x₀ : X) (options : Options R) : (Bool×Bool)
  assessConvergence (state : S) (d : ObjectiveFunction R X) (options : Options R) : (Bool×Bool×Bool×Bool)

  updateState (d : ObjectiveFunction R X) (state : S) (method : Method) : (S×Bool)
  updateG (d : ObjectiveFunction R X) (state : S) (method : Method) : S
  updateH (d : ObjectiveFunction R X) (state : S) (method : Method) : S

  pick_best_x (f_inc_pick : Bool) (state : S) : X
  pick_best_f (f_inc_pick : Bool) (state : S) (d : ObjectiveFunction R X) : R
  x_abschange (state : S) : R
  x_relchange (state : S) : R
  f_abschange (d : ObjectiveFunction R X) (state : S) : R
  f_relchange (d : ObjectiveFunction R X) (state : S) : R
  g_residual (d : ObjectiveFunction R X) (state : S) : R

  f_calls (d : ObjectiveFunction R X) (state : S) : ℕ
  g_calls (d : ObjectiveFunction R X) (state : S) : ℕ
  h_calls (d : ObjectiveFunction R X) (state : S) : ℕ

export AbstractOptimizerState (initialConvergence assessConvergence updateState updateG updateH
       pick_best_x pick_best_f x_abschange x_relchange f_abschange f_relchange g_residual
       f_calls g_calls h_calls)

variable {R X}


variable (R X)
structure MultivariateOptimizationResults where
    method : Method
    initial_x : X
    minimizer : X
    minimum : R
    iterations : ℕ
    iteration_converged : Bool
    x_converged : Bool
    x_abstol : R
    x_reltol : R
    x_abschange : R -- Tc
    x_relchange : R -- Tc
    f_converged : Bool
    f_abstol : R
    f_reltol : R
    f_abschange : R -- Tc
    f_relchange : R -- Tc
    g_converged : Bool
    g_abstol : R
    g_residual : R -- Tc
    f_increased : Bool
    -- trace::M
    f_calls : ℕ
    g_calls : ℕ
    h_calls : ℕ
    ls_success : Bool
    time_limit? : Option ℕ
    time_run : ℕ
    -- stopped_by::Tsb


variable {R X}


variable [AbstractOptimizerState R X S]

def optimize
    (d : ObjectiveFunction R X) (x₀ : X)
    (method : Method)
    (options : Options R)
    (state₀ : S) :
    IO (MultivariateOptimizationResults R X) := do

  let t₀ ← IO.monoNanosNow
  --  tr = OptimizationTrace{typeof(value(d)), typeof(method)}()
  -- tracing = options.store_trace || options.show_trace || options.extended_trace || options.callback !== nothing
  let mut stopped := false
  let mut stopped_by_callback := false
  let mut stopped_by_time_limit := false
  let mut f_limit_reached := false
  let mut g_limit_reached := false
  let mut h_limit_reached := false
  let mut x_converged := false
  let mut f_converged := false
  let mut g_converged := false
  let mut f_increased := false
  let mut counter_f_tol := 0

  let mut state := state₀

  (f_converged, g_converged) := initialConvergence d state x₀ options
  let mut converged := f_converged || g_converged

  let mut iteration := 0

  -- options.show_trace && print_header(method)
  let mut _time ← IO.monoNanosNow
  --  trace!(tr, d, state, iteration, method, options, _time-t0)
  let mut ls_success := true

  while !converged && !stopped && iteration < options.iterations do
    iteration += 1
    (state, ls_success) := updateState d state method
    if !ls_success then
      break
    state := updateG d state method
    (x_converged, f_converged, g_converged, f_increased) := assessConvergence state d options
    counter_f_tol := if f_converged then counter_f_tol+1 else 0
    converged := x_converged || g_converged || (counter_f_tol > options.successive_f_tol)
    if !(converged && method.isNewton) && !(method.isNewtonTrustRegion) then
       state := updateH d state method
    -- if tracing then
    --     -- update trace; callbacks can stop routine early by returning true
    --     stopped_by_callback = trace!(tr, d, state, iteration, method, options, time()-t0)
    _time ← IO.monoNanosNow
    if let some time_limit := options.time_limit? then
      stopped_by_time_limit := _time - t₀ > time_limit
    -- f_limit_reached = options.f_calls_limit > 0 && f_calls(d) >= options.f_calls_limit ? true : false
    -- g_limit_reached = options.g_calls_limit > 0 && g_calls(d) >= options.g_calls_limit ? true : false
    -- h_limit_reached = options.h_calls_limit > 0 && h_calls(d) >= options.h_calls_limit ? true : false

    if (f_increased && !options.allow_f_increases) || stopped_by_callback ||
        stopped_by_time_limit || f_limit_reached || g_limit_reached || h_limit_reached then
        stopped := true

    -- if method isa NewtonTrustRegion
    --     # If the trust region radius keeps on reducing we need to stop
    --     # because something is wrong. Wrong gradients or a non-differentiability
    --     # at the solution could be explanations.
    --     if state.delta ≤ method.delta_min
    --         stopped = true
    --     end
    -- end

    -- if g_calls(d) > 0 && !all(isfinite, gradient(d))
    --     options.show_warnings && @warn "Terminated early due to NaN in gradient."
    --     break
    -- end

    -- if h_calls(d) > 0 && !(d isa TwiceDifferentiableHV) && !all(isfinite, hessian(d))
    --     options.show_warnings && @warn "Terminated early due to NaN in Hessian."
    --     break


    pure ()

  -- Tf = typeof(value(d))
  let f_incr_pick := f_increased && !options.allow_f_increases
  -- Tf = typeof(value(d))
  -- f_incr_pick = f_increased && !options.allow_f_increases
  -- stopped_by =(f_limit_reached=f_limit_reached,
  --              g_limit_reached=g_limit_reached,
  --              h_limit_reached=h_limit_reached,
  --              time_limit=stopped_by_time_limit,
  --              callback=stopped_by_callback,
  --              f_increased=f_incr_pick)


  return {
    method := method
    initial_x := x₀
    minimizer := pick_best_x R f_incr_pick state
    minimum := pick_best_f f_incr_pick state d
    iterations := iteration
    iteration_converged := iteration == options.iterations
    x_converged := x_converged
    x_abstol := options.x_abstol
    x_reltol := options.x_reltol
    x_abschange := x_abschange X state
    x_relchange := x_relchange X state
    f_converged := f_converged
    f_abstol := options.f_abstol
    f_reltol := options.f_reltol
    f_abschange := f_abschange d state
    f_relchange := f_relchange d state
    g_converged := g_converged
    g_abstol := options.g_abstol
    g_residual := g_residual d state
    f_increased := f_increased
    f_calls := f_calls d state
    g_calls := g_calls d state
    h_calls := h_calls d state
    ls_success := ls_success
    time_limit? := options.time_limit?
    time_run := _time - t₀
  }
