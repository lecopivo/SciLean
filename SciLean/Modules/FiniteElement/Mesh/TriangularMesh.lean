import SciLean.Data.Mesh.PrismaticMesh
import SciLean.Data.DataArray

namespace SciLean

structure TriangularSet.FaceData where
  pointCount : Nat
  edgeCount  : Nat
  triangleCount : Nat

  edgePoints    : (Fin pointCount)^{edgeCount, 2}
  triangleEdges : (Fin edgeCount)^{triangleCount, 3}

  -- TODO: Add proposition that it is consistent

open Prism in
structure TriangularSet.CofaceData extends FaceData where
  pointEdges     : ArrayN (Array (Inclusion point segment × Fin edgeCount)) pointCount
  pointTriangles : ArrayN (Array (Inclusion point triangle × Fin triangleCount)) pointCount
  edgeTriangles  : ArrayN (Array (Inclusion segment triangle × Fin triangleCount)) edgeCount


def TriangularSet.FaceData.fromTriangles {pointCount triangleCount}
  (trianglePoints : (Fin pointCount)^{triangleCount,3}) : TriangularSet.FaceData := Id.run do

  -- why does qsort need Inhabited?
  have : Fact (pointCount ≠ 0) := sorry_proof
  have : Fact (triangleCount ≠ 0) := sorry_proof

  -- create a bit array of edges and their local index to
  let mut edges : Array ((Fin pointCount × Fin pointCount) × (Array (Fin triangleCount × Fin 3))) := #[]
  for (i,_) in Enumtype.fullRange (Fin triangleCount) do
    let (p0, p1, p2) := sort3 (trianglePoints[i,0]) (trianglePoints[i,1]) (trianglePoints[i,2])
    edges := edges |>.push ((p0, p1), #[(i,0)])
                   |>.push ((p0, p2), #[(i,1)])
                   |>.push ((p1, p2), #[(i,2)])

  -- sort edges
  edges := edges.qsort (λ x y => x.1.1<y.1.1 ∨ (x.1.1 = y.1.1 ∧ x.1.2 < y.1.2))
  -- remove duplicate edges and collect neighbouring triangles
  edges := edges.foldl (λ a b =>
    let last := a[a.size-1]!
    if last.1 = b.1 then
      a.set! (a.size-1) (last.1, last.2.append b.2)
    else
      a.push b) #[edges[0]!] (start := 1)

  let edgeCount := edges.size
  let mut triangleEdges : (Fin edgeCount)^{triangleCount, 3} := λ [i] => ⟨0, sorry_proof⟩
  let mut edgePoints    : (Fin pointCount)^{edgeCount, 2}    := λ [i] => ⟨0, sorry_proof⟩
  for h : i in [0:edgeCount] do
    let i : Fin edgeCount := ⟨i,h.2⟩
    edgePoints[(i,(0 : Fin 2))] := edges[i].1.1
    edgePoints[(i,(1 : Fin 2))] := edges[i].1.2
    for h : j in [0:edges[i].2.size] do
      let j : Fin _ := ⟨j,h.2⟩
      triangleEdges[edges[i].2[j]] := i


  {
    pointCount := pointCount
    edgeCount := edgeCount
    triangleCount := triangleCount

    edgePoints := edgePoints
    triangleEdges := triangleEdges
  }

-- TODO: Define few predicates on TriangularSet.FaceData
--     1. it is consistent
--     2. it is a manifold i.e. each edge has one or two neighbours
--     3. does not have boundary i.e. every edge has at least two neighbours (does not have to be manifold e.g. double bubble)

open Prism in
def TriangularSet (data : TriangularSet.FaceData) : PrismaticSet :=
{
  Elem := λ P =>
    match P with
    | ⟨.point, _⟩ => Fin data.pointCount
    | ⟨.cone .point, _⟩  => Fin data.edgeCount
    | ⟨.cone (.cone .point), _⟩ => Fin data.triangleCount
    | _ => Empty

  face := λ {Q P} ι e =>
    match Q, P, ι with
    -- faces of a point
    | ⟨.point, _⟩, ⟨.point, _⟩, ⟨.point, _, _⟩ => e

    -- facese of an edge
    -- TODO: use conversion of a face to Fin
    |  ⟨.point, _⟩,  ⟨.cone .point, _⟩, ⟨.base .point, _, _⟩ => data.edgePoints[e,0]
    |  ⟨.point, _⟩,  ⟨.cone .point, _⟩,  ⟨.tip .point, _, _⟩ => data.edgePoints[e,1]
    | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩, ⟨.cone .point, _, _⟩ => e

    -- facese of a triangle
    -- TODO: use conversion of a face to Fin
    | ⟨.point, _⟩, ⟨.cone (.cone .point), _⟩, ⟨.base (.base .point), _, _⟩ =>
      let edge := data.triangleEdges[e,0]
      data.edgePoints[edge,0]
    | ⟨.point, _⟩, ⟨.cone (.cone .point), _⟩, ⟨.base (.tip .point), _, _⟩  =>
      let edge := data.triangleEdges[e,0]
      data.edgePoints[edge,1]
    | ⟨.point, _⟩, ⟨.cone (.cone .point), _⟩, ⟨.tip (.cone .point), _, _⟩  =>
      let edge := data.triangleEdges[e,1]
      data.edgePoints[edge,1]
    |  ⟨.cone .point, _⟩, ⟨.cone (.cone .point), _⟩, ⟨.base (.cone .point), _, _⟩ => data.triangleEdges[e,0]
    |  ⟨.cone .point, _⟩, ⟨.cone (.cone .point), _⟩, ⟨.cone (.base .point), _, _⟩ => data.triangleEdges[e,1]
    |  ⟨.cone .point, _⟩, ⟨.cone (.cone .point), _⟩,  ⟨.cone (.tip .point), _, _⟩ => data.triangleEdges[e,1]
    | ⟨.cone (.cone .point), _⟩, ⟨.cone (.cone .point), _⟩, ⟨.cone (.cone .point), _, _⟩ => e

    | _, _, _ =>
      /- In all remaining cases `e` is an element of `Empty` -/
      absurd (a:=True) sorry_proof sorry_proof


  face_comp := sorry_proof
}

open Prism in
instance (data : TriangularSet.CofaceData) : (TriangularSet data.toFaceData).Coface where

  CofaceIndex := λ {Q} e P =>
    match Q, P with
    -- point neighbours
    | ⟨.point, _⟩, ⟨.point, _⟩    => Unit
    | ⟨.point, _⟩, ⟨.cone .point, _⟩  =>
      let e : Fin data.pointCount := reduce_type_of e
      Fin data.pointEdges[e].size
    | ⟨.point, _⟩, ⟨.cone (.cone .point), _⟩ =>
      let e : Fin data.pointCount := reduce_type_of e
      Fin data.pointTriangles[e].size

    -- edge neighbours
    | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩  => Unit
    | ⟨.cone .point, _⟩, ⟨.cone (.cone .point), _⟩ =>
      let e : Fin data.edgeCount := reduce_type_of e
      Fin data.edgeTriangles[e].size

    -- triagnle neighbours
    | ⟨.cone (.cone .point), _⟩, ⟨.cone (.cone .point), _⟩ => Unit

    | _, _ => Empty

  coface := λ {Q} e P id =>
    match Q, P with

    | ⟨.point, _⟩, ⟨.point, _⟩ =>
      (⟨.point, sorry_proof, sorry_proof⟩, e)
    | ⟨.point, _⟩, ⟨.cone .point, _⟩ =>
      data.pointEdges[reduce_type_of e][id]
    | ⟨.point, _⟩, ⟨.cone (.cone .point), _⟩ =>
      data.pointTriangles[reduce_type_of e][id]

    | ⟨.cone .point, _⟩, ⟨.cone .point, _⟩ =>
      let e : Fin data.edgeCount := e
      (⟨.cone .point, sorry_proof, sorry_proof⟩, e)
    | ⟨.cone .point, _⟩, ⟨.cone (.cone .point), _⟩ =>
      data.edgeTriangles[reduce_type_of e][id]

    | ⟨.cone (.cone .point), _⟩, ⟨.cone (.cone .point), _⟩ =>
      let e : Fin data.triangleCount := e
      (⟨.cone (.cone .point), sorry_proof, sorry_proof⟩, e)

    | _, _ =>
      /- In all remaining cases `id` is an element of `Empty` -/
      absurd (a:=True) sorry_proof sorry_proof

  face_coface := sorry_proof


structure TriangularMesh.PointData (dim : Nat) extends TriangularSet.FaceData where
  pos : ℝ^{pointCount, dim}

def TriangularMesh (dim) (data : TriangularMesh.PointData dim) : PrismaticMesh (ℝ^{dim}) :=
  PrismaticMesh.mk (X:=ℝ^{dim}) (TriangularSet data.toFaceData)
  (toPos := λ ⟨P,e,x⟩ =>
    let p : Inclusion Prism.point P → ℝ^{dim} := λ ι =>
      let pt := (TriangularSet data.toFaceData).face ι e
      data.pos[reduce_type_of pt, :]
    P.barycentricInterpolate p x)
  (toPos_face := sorry_proof)
