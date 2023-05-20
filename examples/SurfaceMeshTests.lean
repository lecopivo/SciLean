import SciLean.Data.Mesh.SurfaceMesh
import LSpec


def testTetrahedron : IO Bool := do
  let base0 : V3 := V3.mk 0 0 0
  let base1 : V3 := V3.mk 2 0 0
  let base2 : V3 := V3.mk 1 1 0
  let apex : V3 := V3.mk 0 0 1
  let indices : Array (Index ``Vertex) := #[]
  let indices := indices.append #[0, 1, 2] -- base
  let indices := indices.append #[0, 1, 3] -- (0, 1) to apex tri
  let indices := indices.append #[0, 2, 3] -- ditto
  let indices := indices.append #[1, 2, 3] -- ditto
  let mesh ← match SurfaceMesh.build #[base0, base1, base2, apex] indices with
    | .error err => IO.println s!"ERROR: {err}"; return false
    | .ok mesh => pure mesh
  IO.println s!"tetrahedron #vertices: {mesh.vertices.size}"
  IO.println s!"tetrahedron #edges: {mesh.edges.size}"
  IO.println s!"tetrahedron  #faces: {mesh.faces.size}"
  assert! mesh.eulerCharacteristic == 2
  return true

def testSphere : IO Bool := do
  let sphereData ← SurfaceMesh.fromOFFFile "data/sphere_s3.off" -- load mesh
  IO.println s!"sphere #vertices: {sphereData.vertices.size}"
  IO.println s!"sphere #edges: {sphereData.edges.size}"
  IO.println s!"sphere  #faces: {sphereData.faces.size}"
  assert! sphereData.eulerCharacteristic == 2 -- homeomorphic to a sphere.
  return True

def testBunny : IO Bool := do
  let bunnyData ← SurfaceMesh.fromOFFFile "data/bunny.off" -- load mesh
  IO.println s!"bunny #vertices: {bunnyData.vertices.size}"
  IO.println s!"bunny #edges: {bunnyData.edges.size}"
  IO.println s!"bunny  #faces: {bunnyData.faces.size}"
  assert! bunnyData.eulerCharacteristic == 2 -- homeomorphic to a sphere.
  return True

-- build an n-torus and check its eutler characteristic.
-- Also check that we have the correct generators.
-- TODO
def testNTorus (n : Nat) : IO Bool := do
  return True

def main := do
  let ret ← testTetrahedron
  assert! ret

  let ret ← testSphere
  assert! ret

  let ret ← testBunny
  assert! ret
