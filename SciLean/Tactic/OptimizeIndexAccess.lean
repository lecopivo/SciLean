import Lean
import SciLean.Data.DataArray
import SciLean.Data.IndexType

import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.OptimizeIndexAccessInit

namespace SciLean

open Lean Meta

open IndexType in
@[optimize_index_access]
theorem IndexType.toFin_prod {I J} [IndexType I] [IndexType J] (i : I) (j : J) :
    IndexType.toFin (i, j) = ⟨(toFin i).1 + size I * (toFin j).1, sorry_proof⟩ :=
  rfl

@[optimize_index_access]
theorem _root_.LeanColls.IndexType.toFin_Fin (i : Fin n) :
    IndexType.toFin i = i :=
  rfl


attribute [optimize_index_access]
  GetElem.getElem DataArrayN.get
  Fin.cast
  Size.size

macro "optimize_index_access" : conv =>
  `(conv| simp (config:={zeta:=false}) only
      [↓ refinedRewritePre, refinedRewritePost, optimize_index_access])
