import SciLean.Data.Mesh.SurfaceMesh
import LSpec


def main := do
  let _bunnyData ← SurfaceMesh.fromOFFFile "data/bunny.off" -- load mesh
