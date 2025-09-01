import SciLean.Data.Mesh.Prism

namespace SciLean
open Prism

#check Face



-- run over all dimensions and basic prisms
#eval show Lean.CoreM Unit from do

  let P := Prism.cube
  let dim := 1
  let mut i := 0

  for e in fullRange (Face P (some dim)) do
    if e.toFin.1 ≠ i then
      throwError "Mismatch between forIn interation `{i}` and index `{e.toFin}` on face {e.repr.toString} for prism {P.repr.toString}"

    IO.println s!"edge: {e.repr.toString} | id: {e.toFin}"

    i := i + 1


-- run over all dimensions and basic prisms
#eval show Lean.CoreM Unit from do

  let P := Prism.pyramid
  let Q := Prism.triangle
  let mut i : Nat := 0

  for e in fullRange (Inclusion Q P) do
    IO.println s!"face: {e.repr.toString} | id: {i} | dim: {e.repr.toPrism.toCanonical.toString}"
    i := i + 1



-- def testFaceIterable (P : Prism) : IO Unit := do

--   for fDim in [0:P.dim+1] do

--     for face in
