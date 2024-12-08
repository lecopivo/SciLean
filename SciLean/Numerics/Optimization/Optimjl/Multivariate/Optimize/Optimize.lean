import SciLean.Numerics.Optimization.Optimjl.Utilities.Types

/-! Port of Optim.jl, file src/multivariate/optimize/optimize.jl

github link:
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/multivariate/optimize/optimize.jl
-/

namespace SciLean.Optimjl

variable
  {R : Type} [RealScalar R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {S M : Type}

variable [AbstractOptimizerState R X S M]

def optimize
    (d : ObjectiveFunction R X) (x₀ : X)
    (method : M)
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

  (f_converged, g_converged) := initialConvergence M d state x₀ options
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
    state := updateFG d state method
    (x_converged, f_converged, g_converged, f_increased) := assessConvergence M state d options
    counter_f_tol := if f_converged then counter_f_tol+1 else 0
    converged := x_converged || g_converged || (counter_f_tol > options.successive_f_tol)
    -- if !(converged && method.isNewton) && !(method.isNewtonTrustRegion) then
    if true then
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
    initial_x := x₀
    minimizer := pick_best_x R M f_incr_pick state
    minimum := pick_best_f M f_incr_pick state d
    iterations := iteration
    iteration_converged := iteration == options.iterations
    x_converged := x_converged
    x_abstol := options.x_abstol
    x_reltol := options.x_reltol
    x_abschange := x_abschange X M state
    x_relchange := x_relchange X M state
    f_converged := f_converged
    f_abstol := options.f_abstol
    f_reltol := options.f_reltol
    f_abschange := f_abschange M d state
    f_relchange := f_relchange M d state
    g_converged := g_converged
    g_abstol := options.g_abstol
    g_residual := g_residual M d state
    f_increased := f_increased
    f_calls := f_calls M d state
    g_calls := g_calls M d state
    h_calls := h_calls M d state
    ls_success := ls_success
    time_limit? := options.time_limit?
    time_run := _time - t₀
  }
