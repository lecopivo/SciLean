import SciLean.Data.Mesh.SurfaceMesh
import LSpec


def main := do
  let sphereData ← SurfaceMesh.fromOFFFile "data/sphere_s3.off" -- load mesh
  IO.println s!"sphere #vertices: {sphereData.vertices.size}"
  IO.println s!"sphere #edges: {sphereData.edges.size}"
  IO.println s!"sphere  #faces: {sphereData.faces.size}"
  assert! sphereData.eulerCharacteristic == 2 -- homeomorphic to a sphere.
  
  let bunnyData ← SurfaceMesh.fromOFFFile "data/bunny.off" -- load mesh
  IO.println s!"bunny #vertices: {bunnyData.vertices.size}"
  IO.println s!"bunny #edges: {bunnyData.edges.size}"
  IO.println s!"bunny  #faces: {bunnyData.faces.size}"
  assert! bunnyData.eulerCharacteristic == 2 -- homeomorphic to a sphere.