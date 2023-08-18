/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Trace classes for DDG module.

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.SlimCheck.Testable`.
-/

import Lean
open Lean

initialize registerTraceClass `SciLean.Modules.DDG.SurfaceMesh
