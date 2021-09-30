import Lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic


open Lean 
open Lean.Meta
open Lean.Elab.Tactic

--- Add an assumption 
syntax (name := subintro) "solver_assume" notFollowedBy("|") (colGt term:max)* : tactic

--- Solve the current Prop goal by adding it to the list of assumptions/promisses
syntax (name := assume_this) "assume_this" notFollowedBy("|") (colGt term:max)* : tactic

--- Solve the current Decidable Prop goal by adding a runtime check
syntax (name := check_this) "check_this" notFollowedBy("|") (colGt term:max)* : tactic

