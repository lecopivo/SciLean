import SciLean.Tactic.CompiledTactics
import SciLean.Tactic.LSimp.Elab

open Lean


def Impl {α} (_ : α) := α

def finish_impl {α} {a : α} : Impl a := a


def foo1 : Impl (let a := id 1; a) := by apply finish_impl
def foo2 : Impl (foo1) := by
  unfold foo1 finish_impl
  (conv => lsimp (config:={memoize:=false}) only [])
  apply finish_impl
