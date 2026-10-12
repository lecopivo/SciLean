/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
module

public import Lean.Meta.Tactic.Simp.Types

public meta import Lean.Meta.Tactic.Simp.Types

public import Mathlib.Tactic.FunProp.Types

public meta import Mathlib.Tactic.FunProp.Types

@[expose] public meta section


/-!
## `funTrans`
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunTrans

instance : Inhabited FunProp.Context := ⟨{}⟩

structure Context where
  funPropContext : FunProp.Context := {}
deriving Inhabited

initialize funTransContext : IO.Ref Context ← IO.mkRef {}
