/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Surface Mesh based on discrete differential geometry.
https://github.com/GeometryCollective/geometry-processing-js/blob/c7ea47ae808979a5361e3fcd61bf921a194bf897/core/mesh.js#L3-L213
-/

import SciLean.Data.DataArray.FloatN

open Lean Data


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
  prev : Index `Halfedge := .invalid
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
  positions  : Array SciLean.Float3 := {}
  vertices   : Array Vertex := {}
  edges      : Array Edge := {}
  faces      : Array Face := {}
  corners    : Array Corner := {}
  halfedges  : Array Halfedge := {}
  boundaries : Array Boundary := {}

instance : Inhabited SurfaceMesh where default := {}


/-
Computes the euler characteristic of this mesh.
-/
def SurfaceMesh.eulerCharacteristic (s: SurfaceMesh) : Int :=
  (s.vertices.size : Int) - (s.edges.size : Int) + (s.faces.size : Int)

-- # Monad to build surface meshes.
inductive MeshBuilderError
| nonManifoldEdge (i j : Index ``Vertex)
| parseError (err : String)
deriving Inhabited

def MeshBuilderError.toString : MeshBuilderError → String
| nonManifoldEdge i j => s!"non-manifold edge {i} → {j}"
| parseError err => err

instance : ToString MeshBuilderError where
  toString := MeshBuilderError.toString

abbrev MeshBuilderM (α : Type) := EStateM MeshBuilderError SurfaceMesh α

-- ### Vertex accessors
def MeshBuilderM.newVertex : MeshBuilderM (Index ``Vertex) :=
  fun s =>
   let ix := s.vertices.size
   let data : Vertex := {}
   let data := { data with index := ix }
   EStateM.Result.ok ix { s with vertices := s.vertices.push data }

def MeshBuilderM.modifyVertex (ix : Index ``Vertex)
  (fn : Vertex → Vertex) : MeshBuilderM Vertex :=
  fun s =>
    assert! (ix < s.vertices.size)
    let out := fn s.vertices[ix]!
    EStateM.Result.ok out { s with vertices := s.vertices.set! ix out }

/-
def MeshBuilderM.getVertex (ix : Index ``Vertex) : MeshBuilderM Vertex :=
  MeshBuilderM.modifyVertex ix id

def MeshBuilderM.setVertex (ix : Index ``Vertex) (v : Vertex) : MeshBuilderM Vertex :=
  MeshBuilderM.modifyVertex ix (fun _ => v)
-/
-- ### Edge accessors
def MeshBuilderM.newEdge : MeshBuilderM (Index ``Edge) :=
  fun s =>
   let ix := s.edges.size
   let data : Edge := {}
   let data : Edge := { data with index := ix }
   EStateM.Result.ok ix { s with edges := s.edges.push data }

def MeshBuilderM.modifyEdge (ix : Index ``Edge)
  (fn : Edge → Edge) : MeshBuilderM Edge :=
  fun s =>
    let out := fn s.edges[ix]!
    EStateM.Result.ok out { s with edges := s.edges.set! ix out }

def MeshBuilderM.modifyEdge_ (ix : Index ``Edge)
  (fn : Edge → Edge) : MeshBuilderM Unit := do
  let _ ← MeshBuilderM.modifyEdge ix fn

def MeshBuilderM.getEdge (ix : Index ``Edge) : MeshBuilderM Edge :=
  MeshBuilderM.modifyEdge ix id

def MeshBuilderM.setEdge (ix : Index ``Edge) (v : Edge) : MeshBuilderM Edge :=
  MeshBuilderM.modifyEdge ix (fun _ => v)

-- ### Halfedge accessors
def MeshBuilderM.newHalfedge : MeshBuilderM (Index ``Halfedge) :=
  fun s =>
   let ix := s.halfedges.size
   let data : Halfedge := { (default : Halfedge) with index := ix }
   EStateM.Result.ok ix { s with halfedges := s.halfedges.push data }

def MeshBuilderM.modifyHalfedge (ix : Index ``Halfedge)
  (fn : Halfedge → Halfedge) : MeshBuilderM Halfedge :=
  fun s =>
    let out := fn s.halfedges[ix]!
    EStateM.Result.ok out { s with halfedges := s.halfedges.set! ix out }

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
   let ix := s.faces.size
   let data : Face := {}
   let data := { data with index := ix }
   EStateM.Result.ok ix { s with faces := s.faces.push data }

-- TODO: modify anything with the typeclass [IsPointerTo ``Face].
def MeshBuilderM.modifyFace (ix : Index ``Face)
  (fn : Face → Face) : MeshBuilderM Face :=
  fun s =>
    let out := fn s.faces[ix]!
    EStateM.Result.ok out { s with faces := s.faces.set! ix out }

def MeshBuilderM.modifyFace_ (ix : Index ``Face)
  (fn : Face → Face) : MeshBuilderM Unit := do
  let _ ← MeshBuilderM.modifyFace ix fn

def MeshBuilderM.getFace (ix : Index ``Face) : MeshBuilderM Face :=
  MeshBuilderM.modifyFace ix id

def MeshBuilderM.setFace (ix : Index ``Face) (v : Face) : MeshBuilderM Face :=
  MeshBuilderM.modifyFace ix (fun _ => v)

-- ### Corner accessors
def MeshBuilderM.newCorner : MeshBuilderM (Index ``Corner) :=
  fun s =>
   let ix := s.corners.size
   let data : Corner := {}
   let data := { data with index := ix }
   EStateM.Result.ok ix { s with corners := s.corners.push data }

-- TODO: modify anything with the typeclass [IsPointerTo ``Corner].
def MeshBuilderM.modifyCorner (ix : Index ``Corner)
  (fn : Corner → Corner) : MeshBuilderM Corner :=
  fun s =>
    let out := fn s.corners[ix]!
    EStateM.Result.ok out { s with corners := s.corners.set! ix out }

def MeshBuilderM.modifyCorner_ (ix : Index ``Corner)
  (fn : Corner → Corner) : MeshBuilderM Unit := do
  let _ ← MeshBuilderM.modifyCorner ix fn

def MeshBuilderM.getCorner (ix : Index ``Corner) : MeshBuilderM Corner :=
  MeshBuilderM.modifyCorner ix id

def MeshBuilderM.setCorner (ix : Index ``Corner) (v : Corner) : MeshBuilderM Corner :=
  MeshBuilderM.modifyCorner ix (fun _ => v)




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

partial def MeshBuilderM.build_
  (positions : Array (SciLean.Float3)) (indices : Array (Index ``Vertex)) : MeshBuilderM Unit := do {
  let mut existingHalfedges :
      Std.HashMap (Index `Vertex × Index `Vertex) (Index `Halfedge) := {};
  let mut edgeCount :
    Std.HashMap (Index `Vertex × Index `Vertex) Nat := {};
  modify (fun s => { s with positions := positions }); -- store positions in the SurfaceMesh

  -- pre-allocate all vertices for random access via faces.
  for _ in Array.range positions.size do {
      let _ ← newVertex;
  }
  assert! (indices.size % 3 == 0);
  for i in Array.range (indices.size / 3) do {
    let I := i * 3;
    let f ← newFace;
    -- create a halfedge for each edge of the newly created face
    for _ in Array.range 3 do {
      let _ ← newHalfedge; -- make the new half edges
    }
    for J in Array.range 3 do {
      -- current halfedge goes from vertex i to vertex j
      let K : Nat := (J + 1) % 3;
      let i := I + J;
      let j := I + K;
      -- set the current halfedge's attributes
      let _ ← modifyHalfedge_ i (fun he => { he with next := j });
      let _ ← modifyHalfedge_ i (fun he => { he with prev := I + (J + 3 - 1) % 3 });
      let _ ← modifyHalfedge_ i (fun he => { he with onBoundary := false });
      -- hasTwinHalfedge.set(h, false);

      -- point the new halfedge and vertex i to each other
      assert! (i < indices.size);
      let _ ← modifyHalfedge i (fun he => { he with vertex := indices[i]! });
      let _ ← modifyVertex indices[i]! (fun v => { v with halfedge := i });

      -- point the new halfedge and face to each other
      let _ ← modifyHalfedge i (fun he => { he with face := f });
      let _ ← modifyFace f (fun f => { f with halfedge := i });

      -- swap if (i > j) to maintain invariant that (i <= j)
      let edgeKey :=
        let vi := indices[i]!;
        let vj := indices[j]!
        if vi <= vj then (vi, vj) else (vj, vi);
      assert! edgeKey.fst <= edgeKey.snd
      let hIx := I + J; -- TODO: cleanup
      let oldEdgeCount := edgeCount.getD edgeKey 0;
      match existingHalfedges[edgeKey]? with
      | .some twin' => {
        -- if a halfedge between vertex i and j has been
        -- created in the past, then it is the twin halfedge
        -- of the current halfedge
        let _ ← modifyHalfedge_ hIx (fun h => { h with twin := twin' });
        let _ ← modifyHalfedge_ twin' (fun twin => { twin with twin := hIx });
        let twinEdge ← getHalfedge twin';
        let _ ← modifyHalfedge_ hIx (fun h => { h with edge := twinEdge.edge });
        edgeCount := edgeCount.insert edgeKey (oldEdgeCount + 1);
      }
      | .none => {
        let e ← newEdge;
        let _ ← modifyEdge e (fun e => { e with halfedge := hIx });
        let _ ← modifyHalfedge_ hIx (fun h => { h with edge := e });
        edgeCount := edgeCount.insert edgeKey 1;
      };
      -- record the newly created edge and halfedge from vertex i to j
      existingHalfedges := existingHalfedges.insert edgeKey hIx;

      if edgeCount.getD edgeKey 0 > 2 then {
        throw <| MeshBuilderError.nonManifoldEdge i j;
      }
    }
  }
  -- create and insert boundary halfedges and "imaginary" faces for boundary cycles
  -- also create and insert corners.
  -- Note that every vertex corresponds to the halfedge from that vertex to
  --   the next one in the triangle.
  for i in Array.range indices.size do {
    let h ← getHalfedge i;
    -- If a halfedge has no twin halfedge, create a new face and
    -- link it the corresponding boundary cycle
    -- TODO: move this function into the function.
    if  h.twin.isNone then {
      MeshBuilderM.makeBoundary h #[] h
    }
    -- point the newly created corner and its halfedge to each other
    -- TODO: think about the maths here.
    if ! (← getHalfedge i).onBoundary then {
      let cIx ← newCorner;
      let _ ← modifyCorner cIx (fun c => { c with halfedge := h.index });
      let _ ← modifyHalfedge h.index (fun h => { h with corner := cIx });
    }
  let _ ← assertNoIsolatedVertices;
  let _ ← assertNoIsolatedFaces;
  let _ ← assertNoNonManifoldVertices;
  }
}
def MeshBuilderM.run (mb : MeshBuilderM Unit) : Except MeshBuilderError SurfaceMesh :=
  let emptySurfaceMesh : SurfaceMesh := {}
  match EStateM.run mb emptySurfaceMesh with
  | .ok () surfaceMesh => .ok surfaceMesh
  | .error  err _ => .error err


def SurfaceMesh.build (positions: Array (SciLean.Float3)) (indices: Array (Index ``Vertex)) :
  Except MeshBuilderError SurfaceMesh :=
  (MeshBuilderM.build_ positions indices).run

def SurfaceMesh.build' (positions: Array (SciLean.Float3)) (indices: Array (Index ``Vertex)) :
  Option SurfaceMesh :=
  (build positions indices).toOption

def SurfaceMesh.build! (positions: Array (SciLean.Float3)) (indices: Array (Index ``Vertex)) :
  SurfaceMesh := (build' positions indices).get!

/-
-- TODO: figure out code organization for widgets.
@[widget_module]
def Mesh : Component SurfaceMesh where
  javascript := include_str "../build" / "js" / "mesh.js"
-/

/- Random mesh generation -/

/-- Generate a random floating point number in [0, 1] -/
def randFloat01 [G : RandomGen γ] (gen : γ) : Float × γ := Id.run do
  let (val, gen) := G.next gen
  let (lo, hi) := G.range gen
  return ((Float.ofNat <| val - lo) / (Float.ofNat <| hi - lo), gen)

/-- Create a random vertex with coordinates sampled from uniform [0, 1] -/
def randVertex01 [RandomGen γ] (gen : γ) : SciLean.Float3 × γ := Id.run do
  let (val1, gen) := randFloat01 gen
  let (val2, gen) := randFloat01 gen
  let (val3, gen) := randFloat01 gen
  return ({ x := val1, y := val2, z := val3 }, gen)


/-- Create `nvertices` random vertices with coordinates sampled from [-scale/2, scale/2] -/
def randVertices [RandomGen γ]
 (gen : γ) (nvertices : Nat) (scale : Float := 10) : (Array (SciLean.Float3)) × γ := Id.run do
  let mut out : Array (SciLean.Float3) := #[]
  let mut gen := gen
  for _ in Array.range nvertices do
    let (vertex, gen') := randVertex01 gen; gen := gen'
    let vertex : (SciLean.Float3) := ⊞ i => (vertex[i] - 0.5) * scale
    out := out.push vertex
  return (out, gen)


/-- Create a random triangle face with three random vertices with indexes `[0..nvertices)` -/
def randTriFace [RandomGen γ] (gen : γ) (nvertices : Nat) : (Array Nat) × γ := Id.run do
  let (v1, gen) := randNat gen 0 (nvertices-1);
  let (v2, gen) := randNat gen 0 (nvertices-1);
  let (v3, gen) := randNat gen 0 (nvertices-1);
  return (#[v1, v2, v3], gen)

/-- Create a random mesh with `nfaces` random faces. Each face is generated by `randTriFace` -/
def randTriFaces [RandomGen γ] (gen : γ) (nvertices : Nat) (nfaces : Nat) : (Array Nat) × γ := Id.run do
  let mut out : Array Nat := #[]
  let mut gen := gen
  for _ in Array.range nfaces do
    let (face, gen') := randTriFace gen nvertices; gen := gen'
    out := out.append face
  return (out, gen)

/-- Create a random mesh with `nvertices` vertices and `nfaces` faces -/
def SurfaceMesh.rand [RandomGen γ] (gen : γ) (nvertices : Nat) (nfaces : Nat) :
  (Except MeshBuilderError SurfaceMesh) × γ := Id.run do
  let (vs, gen) := randVertices gen nvertices
  let (fs, gen) := randTriFaces gen nvertices nfaces
  return (SurfaceMesh.build vs fs, gen)


/-- Coerce a list of reals into a vector. Throws a ParseError if length of list is not 3 -/
def V3.ofList : List Float → MeshBuilderM (SciLean.Float3)
| [x, y, z] => pure { x := x, y := y, z := z }
| xs => throw <| MeshBuilderError.parseError s!"unable to convert list to vertex '{xs}'"

def V3.ofArray (xs : Array Float) : MeshBuilderM (SciLean.Float3) :=
  return (⟨xs[0]!, xs[1]!, xs[2]!⟩)

/-- Load the mesh data from a .OFF format string -/
def SurfaceMesh.fromOFFString (lines : Array String) : MeshBuilderM Unit := do
  let mut vertices : Array (SciLean.Float3) := #[]
  let mut faces : Array Nat := #[]
  let mut i := 0
  if lines[i]!.trim != "OFF"
  then throw <| MeshBuilderError.parseError s!"expected 'OFF' on line {i+1}. but found '{lines[i]!}' which is not .OFF"
  i := i + 1

  let [n_vertices, n_faces, _n_edges] := lines[i]!.trim.splitOn " "
    | throw <| MeshBuilderError.parseError s!"expected number of vertices, faces, edges information on line {i+1}, but found '{lines[i]!}'"
  i := i + 1

  let .some n_vertices := n_vertices.toNat?
    | throw <| MeshBuilderError.parseError s! "unable to parse num vertices {n_vertices}"

  let .some n_faces := n_faces.toNat?
    | throw <| MeshBuilderError.parseError s! "unable to parse num faces {n_faces}"

  for _ in Array.range n_vertices do
    let coords_raw := lines[i]!.trim.splitOn " "
    let mut v : Array Float := #[]
    for coord in coords_raw do
      let .ok coord := Lean.Json.Parser.num |>.run coord
        | throw <| MeshBuilderError.parseError s!"unable to parse vertex coordinate {coord} on line {i+1}"
        v := v.push coord.toFloat
    vertices := vertices.push (← V3.ofArray v)
    i := i + 1

  for _ in [0:n_faces] do
    let face_indexes_raw := lines[i]!.trim.splitOn " "
    let mut f : Array Nat := #[]
    for ix in face_indexes_raw.drop 1 do
      let .some ix := ix.toNat?
        -- ".. on line {i+1}" -- for some reason adding {i+1} cause stack overflow
        -- this looks like a compiler bug
        | throw <| MeshBuilderError.parseError s!"unable to parse face index {ix} on line ..."
      f := f.push ix
    faces := faces.append f
    i := i + 1
  MeshBuilderM.build_ vertices faces

def SurfaceMesh.fromOFFFile (p : System.FilePath) : IO SurfaceMesh := do
  let out : Except MeshBuilderError SurfaceMesh :=
    (SurfaceMesh.fromOFFString (← IO.FS.lines p)).run
  match out with
  | .ok out => return out
  | .error err => throw <| .userError err.toString
