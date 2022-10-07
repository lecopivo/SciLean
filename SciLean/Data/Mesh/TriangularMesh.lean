import SciLean.Data.Mesh.PrismaticMesh
import SciLean.Data.DataArray

namespace SciLean

#check ℝ^{3}

variable (n m : Nat) [Fact (n≠0)]

example : PlainDataType (Fin n) := by infer_instance

structure TriangularMeshData where
  pointCount : Nat
  edgeCount  : Nat
  triangleCount : Nat

  edgePoints    : (Fin pointCount)^{edgeCount, 2}
  triangleEdges : (Fin edgeCount)^{triangleCount, 3}

  pointEdges     : ArrayN (Array (Fin edgeCount)) pointCount
  pointTriangles : ArrayN (Array (Fin triangleCount)) pointCount
  edgeTriangles  : ArrayN (Array (Fin triangleCount)) edgeCount

-- TODO: Define few predicates on TriangularMeshData
--     1. it is consistent
--     2. it is a manifold i.e. each edge has one or two neighbours
--     3. does not have boundary i.e. every edge has at least two neighbours (does not have to be manifold e.g. double bubble)

open Prism in
def TriangularSet (data : TriangularMeshData) : PrismaticSet :=
{
  Elem := λ P =>
    match P with
    | point    => Fin data.pointCount
    | segment  => Fin data.edgeCount
    | triangle => Fin data.triangleCount
    | _ => Empty

  CofaceIndex := λ {Q} e P =>
    match Q, P with
    -- point neighbours
    | point, point    => Unit
    | point, segment  => Fin data.pointEdges[e].size
    | point, triangle => Fin data.pointTriangles[e].size

    -- edge neighbours
    | segment, segment  => Unit
    | segment, triangle => Fin data.edgeTriangles[e].size

    -- triagnle neighbours
    | triagnle, triangle => Unit

    | _, _ => Empty

  face := λ {Q P} ι e => 
    match Q, P, ι with
    -- faces of a point
    | point, point, ⟨.point, _, _⟩ => e

    -- facese of an edge
    -- TODO: use conversion of a face to Fin
    |  point,  segment, ⟨.base .point, _, _⟩ => data.edgePoints[e,0]
    |  point,  segment,  ⟨.tip .point, _, _⟩ => data.edgePoints[e,1]
    | segment, segment, ⟨.cone .point, _, _⟩ => e

    -- facese of a triangle
    -- TODO: use conversion of a face to Fin
    | point, triangle, ⟨.base (.base .point), _, _⟩ => 
      let edge := data.triangleEdges[e,0]
      data.edgePoints[edge,0]
    | point, triangle, ⟨.base (.tip .point), _, _⟩  =>
      let edge := data.triangleEdges[e,0]
      data.edgePoints[edge,1]
    | point, triangle, ⟨.tip (.cone .point), _, _⟩  => 
      let edge := data.triangleEdges[e,1]
      data.edgePoints[edge,1]
    |  segment, triangle, ⟨.base (.cone .point), _, _⟩ => data.triangleEdges[e,0]
    |  segment, triangle, ⟨.cone (.base .point), _, _⟩ => data.triangleEdges[e,1]
    |  segment, triangle,  ⟨.cone (.tip .point), _, _⟩ => data.triangleEdges[e,1]
    | triangle, triangle, ⟨.cone (.cone .point), _, _⟩ => e

}

  

  #check Prism.point
