namespace SciLean.Tactic

/-- Assuming that the goal is a metavariable, `assign t` assigns term `t` to that metavariable. -/
macro (name := Conv.assign) "assign " t:term : conv =>
  `(conv| tactic => exact (rfl : (_ = $t)))
