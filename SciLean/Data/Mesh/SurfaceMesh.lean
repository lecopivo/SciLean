/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Surface Mesh based on discrete differential geometry.
https://github.com/GeometryCollective/geometry-processing-js/blob/c7ea47ae808979a5361e3fcd61bf921a194bf897/core/mesh.js#L3-L213
-/

import SciLean.Core
import Lean.Data.HashMap

open Lean Data

-- abbrev V3 : Type := ℝ^{3}
-- 3D vector.
structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

/- index of vertices --/
abbrev Index (_name : Name) := Nat
abbrev Index.invalid : Index α := 424242
abbrev Index.ofNat {name : Name} (n : Nat) : Index name := n

structure Vertex where
  index : Index `Vertex := .invalid
  halfedge : Index `Halfedge := .invalid
deriving Inhabited

/-- Half edge data structure -/
structure Halfedge where
  index : Index `Halfedge := .invalid
  next : Index `Halfedge := .invalid
  edge : Index `Edge := .invalid
  twin : Option (Index `Halfedge) := .none
  vertex : Index `Vertex := .invalid
  face : Index `Face := .invalid
  corner : Option (Index `Corner) := .none
  onBoundary : Bool := false
deriving Inhabited

structure Face where
  index : Index `Face := .invalid
  halfedge : Index `Halfedge := .invalid
deriving Inhabited

structure Corner where
  index : Index `Corner := .invalid
  halfedge : Index `Halfedge := .invalid
deriving Inhabited

structure Edge where
  index : Index `Edge := .invalid
  halfedge : Index `Halfedge := .invalid
deriving Inhabited

structure Boundary where
  face : (Index `Face)
  -- gens : Array (Index `Halfedge) := #[]
deriving Inhabited

/-
 * @property {module:Core.Vertex[]} vertices The vertices contained in this mesh.
 * @property {module:Core.Edge[]} edges The edges contained in this mesh.
 * @property {module:Core.Face[]} faces The faces contained in this mesh.
 * @property {module:Core.Corner[]} corners The corners contained in this mesh.
 * @property {module:Core.Halfedge[]} halfedges The halfedges contained in this mesh.
 * @property {module:Core.Face[]} boundaries The boundary loops contained in this mesh.
 * @property {Array.<module:Core.Halfedge[]>} generators An array of halfedge arrays, i.e.,
 -/
structure SurfaceMesh where
  positions  : Array V3 := {}
  vertices   : Array Vertex := {}
  edges      : Array Edge := {}
  faces      : Array Face := {}
  corners    : Array Corner := {}
  halfedges  : Array Halfedge := {}
  boundaries : Array Boundary := {}
  -- generators : Array () [TODO: implement]


/-
Computes the euler characteristic of this mesh.
-/
def SurfaceMesh.eulerCharacteristic (s: SurfaceMesh) : ℕ :=
  s.vertices.size - s.edges.size + s.faces.size

-- # Monad to build surface meshes.
abbrev MeshBuilderM (α : Type) := StateT SurfaceMesh Id α

-- ### Vertex accessors
def MeshBuilderM.newVertex : MeshBuilderM (Index ``Vertex) :=
  fun s =>
   let ix := s.vertices.size
   let data : Vertex := {}
   let data := { data with index := ix }
   (ix, { s with vertices := s.vertices.push data })

def MeshBuilderM.modifyVertex (ix : Index ``Vertex)
  (fn : Vertex → Vertex) : MeshBuilderM Vertex :=
  fun s =>
    let out := fn s.vertices[ix]!
    (out, { s with vertices := s.vertices.set! ix out })

def MeshBuilderM.getVertex (ix : Index ``Vertex) : MeshBuilderM Vertex :=
  MeshBuilderM.modifyVertex ix id

def MeshBuilderM.setVertex (ix : Index ``Vertex) (v : Vertex) : MeshBuilderM Vertex :=
  MeshBuilderM.modifyVertex ix (fun _ => v)

-- ### Edge accessors
def MeshBuilderM.newEdge : MeshBuilderM (Index ``Edge) :=
  fun s =>
   let ix := s.edges.size
   let data : Edge := {}
   let data : Edge := { data with index := ix }
   (ix, { s with edges := s.edges.push data })

def MeshBuilderM.modifyEdge (ix : Index ``Edge)
  (fn : Edge → Edge) : MeshBuilderM Edge :=
  fun s =>
    let out := fn s.edges[ix]!
    (out, { s with edges := s.edges.set! ix out })

def MeshBuilderM.getEdge (ix : Index ``Edge) : MeshBuilderM Edge :=
  MeshBuilderM.modifyEdge ix id

def MeshBuilderM.setEdge (ix : Index ``Edge) (v : Edge) : MeshBuilderM Edge :=
  MeshBuilderM.modifyEdge ix (fun _ => v)

-- ### Halfedge accessors
def MeshBuilderM.newHalfedge : MeshBuilderM (Index ``Halfedge) :=
  fun s =>
   let ix := s.halfedges.size
   let data : Halfedge := { (default : Halfedge) with index := ix }
   (ix, { s with halfedges := s.halfedges.push data })

def MeshBuilderM.modifyHalfedge (ix : Index ``Halfedge)
  (fn : Halfedge → Halfedge) : MeshBuilderM Halfedge :=
  fun s =>
    let out := fn s.halfedges[ix]!
    (out, { s with halfedges := s.halfedges.set! ix out })

def MeshBuilderM.modifyHalfedge_ (ix : Index ``Halfedge)
  (fn : Halfedge → Halfedge) : MeshBuilderM Unit := do 
  let _ ← MeshBuilderM.modifyHalfedge ix fn

def MeshBuilderM.getHalfedge (ix : Index ``Halfedge) : MeshBuilderM Halfedge :=
  MeshBuilderM.modifyHalfedge ix id

def MeshBuilderM.setHalfedge (ix : Index ``Halfedge) (v : Halfedge) : MeshBuilderM Halfedge :=
  MeshBuilderM.modifyHalfedge ix (fun _ => v)

def MeshBuilderM.modifyBoundaries (f : Array Boundary → Array Boundary) : MeshBuilderM Unit :=
  modify (fun s => { s with boundaries := f s.boundaries })

-- ### Face accessors
-- TODO: return the face
def MeshBuilderM.newFace : MeshBuilderM (Index ``Face) :=
  fun s =>
   let ix := s.halfedges.size
   let data : Face := {}
   let data := { data with index := ix }
   (ix, { s with faces := s.faces.push data })

-- TODO: modify anything with the typeclass [IsPointerTo ``Face].
def MeshBuilderM.modifyFace (ix : Index ``Face)
  (fn : Face → Face) : MeshBuilderM Face :=
  fun s =>
    let out := fn s.faces[ix]!
    (out, { s with faces := s.faces.set! ix out })

def MeshBuilderM.modifyFace_ (ix : Index ``Face)
  (fn : Face → Face) : MeshBuilderM Unit := do
  let _ ← MeshBuilderM.modifyFace ix fn

def MeshBuilderM.getFace (ix : Index ``Face) : MeshBuilderM Face :=
  MeshBuilderM.modifyFace ix id

def MeshBuilderM.setFace (ix : Index ``Face) (v : Face) : MeshBuilderM Face :=
  MeshBuilderM.modifyFace ix (fun _ => v)




/-
* Constructs this mesh.
* @method module:Core.Mesh#build
* @param {Object} polygonSoup A polygon soup mesh containing vertex positions and indices.
* @param {module:LinearAlgebra.Vector[]} polygonSoup.v The vertex positions of the polygon soup mesh.
* @param {number[]} polygonSoup.f The indices of the polygon soup mesh.
* @returns {boolean} True if this mesh is constructed successfully and false if not
* (when this mesh contains any one or a combination of the following - non-manifold vertices,
*  non-manifold edges, isolated vertices, isolated faces).

indices: indexes of triangles, where a triangle is a contingous sequence of 3 indexes, of the vertices
  of the triangle.
-/

partial def MeshBuilderM.makeBoundary
  (start : Halfedge)
  (boundaryCycle : Array (Index ``Halfedge))
  (he : Halfedge) : MeshBuilderM Unit :=  do
  let bhIx ← newHalfedge
  let boundaryCycle := boundaryCycle.push bhIx

  -- create new face
  let fIx ← newFace
  -- TODO: check if this notion of boundary is correct?
  modifyBoundaries fun boundaries => boundaries.push { face := fIx : Boundary }


  -- grab the next halfedge along the boundary that does not have a twin halfedge
  let mut nextHe := he
  while nextHe.twin.isSome do {
    nextHe ← getHalfedge (← getHalfedge nextHe.twin.get!).next
  }

  -- Set the current halfedge's attributes
  modifyHalfedge_ bhIx (fun h => { h with vertex := nextHe.index })
  modifyHalfedge_ bhIx (fun h => { h with edge := nextHe.edge })
  modifyHalfedge_ bhIx (fun h => { h with onBoundary := true })

  -- point the new halfedge and face to each other
  modifyHalfedge_ bhIx (fun h => { h with face := fIx })
  modifyFace_ fIx (fun f => { f with halfedge := bhIx })

  -- point the new halfedge and he to each other
  modifyHalfedge_ bhIx (fun h => { h with twin := he.index })
  modifyHalfedge_ bhIx (fun h => { h with twin := he.index })
 -- TODO: allow the `modifyHalfedge_` to take a typeclass called `IsHalfedgeIndex`.
  modifyHalfedge_ he.index (fun h => { h with twin := he.index })

  -- continue walk
  let he := nextHe;
  if he.index == start.index
  then return
  else makeBoundary start boundaryCycle he

partial def MeshBuilderM.assertNoIsolatedVertices : MeshBuilderM Unit := return ()
partial def MeshBuilderM.assertNoIsolatedFaces : MeshBuilderM Unit := return ()
partial def MeshBuilderM.assertNoNonManifoldVertices : MeshBuilderM Unit := return ()

partial def MeshBuilderM.build (positions : Array V3) (indices : Array (Index ``Vertex)) : MeshBuilderM Unit :=
  for i in List.range positions.size do {
    let vix ← newVertex
    -- keeps track of halfedges between existing vertices.
    --   if a halfedge already exists, then we know that the halfedge
    --   we are constructing is a twin.
    let mut existingHalfedges :
      HashMap (Index `Vertex × Index `Vertex) (Index `Halfedge) := {}
    let mut edgeCount :
      HashMap (Index `Vertex × Index `Vertex) Nat := {}
    let mut edgeCount :
    for i in List.range (indices.size / 3) do {
      let I := i * 3
      let f ← newFace
      -- create a halfedge for each edge of the newly created face
      for J in List.range 3 do {
        let _ ← newHalfedge -- make the new half edges
      }
      for J in List.range 3 do { 
        -- current halfedge goes from vertex i to vertex j
        let K := (J + 1) % 3
        let i := I + J
        let j := I + K
        -- set the current halfedge's attributes
        modifyHalfedge i (fun he => { he with next := j })
        modifyHalfedge i (fun he => { he with prev := I + (J + 3 - 1) % 3 })
        modifyHalfedge i (fun he => { he with onBoundary := false })
        -- hasTwinHalfedge.set(h, false);

        -- point the new halfedge and vertex i to each other
        -- let v = indexToVertex.get(i);
        modifyHalfedge i (fun he => { he with vertex := indices[i]! })
        modifyVertex indieces[i]! (fun v => { v with halfedge := i })

        -- point the new halfedge and face to each other
        modifyHalfedge i (fun he => { he with face := f })
        modifyFace f (fun f => { f with halfedge := i })

        -- swap if (i > j) to maintain invariant that (i < j)
        let (i, j) := if i > j then (j, i) else (i, j)
        match existingHalfedges.find (i, j) with
        | .some twin' => { -- primed is pointer.
          -- if a halfedge between vertex i and j has been
          -- created in the past, then it is the twin halfedge
          -- of the current halfedge
          let h' := I + J -- TODO: cleanup
          modifyHalfedge h' (fun h => { h with twin := twin' })
          modifyHalfedge twin' (fun twin => { twin with twin := h' })
          let twinEdge ← getHalfedge twin'
          modifyHalfedge h' (fun h => { h with edge := twinEdge.edge })

          -- TODO: use `modify`.
          edgeCount := edgeCount.insert key <| (edgeCount.get! key) + 1
        }
        | .none => {
          -- create an edge and set its halfedge
          let h := I + J -- TODO: cleanup
          let e ← newEdge
          modifyEdge e (fun e => { e with halfedge := h })
          modifyHalfedge h (fun h => { h with edge := e })
        }
        -- record the newly created edge and halfedge from vertex i to j
        existingHalfedges := existingHalfedges.insert (i, j) h
        -- edgeCount := edgeCount.set (i, j) 1

        if edgeCount.get key > 2 then {
          panic!("Mesh has non-manifold edges!")
          return false
        }
      }
    -- -- create and insert boundary halfedges and "imaginary" faces for boundary cycles
    -- -- also create and insert corners.
    -- -- Note that every vertex corresponds to the halfedge from that vertex to
    -- --   the next one in the triangle.
    -- for i in List.range indices.size do
    --   let h ← getHalfedge i
    --   -- If a halfedge has no twin halfedge, create a new face and
    --   -- link it the corresponding boundary cycle
    --   -- TODO: move this function into the function.
    --   if  h.twin.isNone then
    --     MeshBuilderM.makeBoundary h #[] h

    --   -- point the newly created corner and its halfedge to each other
    --   -- TODO: think about the maths here.
    --   if ! (← getHalfedge i).onBoundary then
    --     let cIx ← newCorner
    --     modifyCorner cIx (fun c => { c with halfedge := h.index })
    --     modifyHalfedge h.index (fun h => { h with corner := cIx })
    -- assertNoIsolatedVertices
    -- assertNoIsolatedFaces
    -- assertNoNonManifoldVertices
    }
  }
  return ()