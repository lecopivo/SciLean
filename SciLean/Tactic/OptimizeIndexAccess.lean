import Lean
import SciLean.Data.DataArray
import SciLean.Data.IndexType

import SciLean.Tactic.RefinedSimp
import SciLean.Tactic.OptimizeIndexAccessInit

namespace SciLean

open Lean Meta

open LeanColls IndexType in
@[optimize_index_access]
theorem _root_.LeanColls.IndexType.toFin_prod {I J} [IndexType I] [IndexType J] (i : I) (j : J) :
    IndexType.toFin (i, j) = ⟨(toFin i).1 * card J + (toFin j).1, sorry_proof⟩ :=
  rfl

@[optimize_index_access]
theorem _root_.LeanColls.IndexType.toFin_Fin (i : Fin n) :
    IndexType.toFin i = i :=
  rfl


attribute [optimize_index_access]
  GetElem.getElem DataArrayN.get
  LeanColls.IndexType.toFin_fromFin LeanColls.IndexType.fromFin_toFin Fin.cast Fin.pair
  IndexType.card

macro "optimize_index_access" : conv =>
  `(conv| simp (config:={zeta:=false}) only
      [↓ refinedRewritePre, refinedRewritePost, optimize_index_access])
