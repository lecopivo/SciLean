/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Tree Cotree algorithm to compute homology generators.
https://github.com/GeometryCollective/geometry-processing-js/blob/c7ea47ae808979a5361e3fcd61bf921a194bf897/projects/vector-field-decomposition/tree-cotree.js
[1] Greedy optimal homotopy and homology generators
-/

import SciLean.Modules.DDG.SurfaceMesh

-- TODO: 'Tree' is already in scope from Mathlib.Data.Tree, but I am not sure
-- *how* it is in scope!
@[reducible]
abbrev IndexTree (name : Lean.Name) := Array (Index name) -- array of parent pointers

def IndexTree.fullyDisconnected (len : Nat) : IndexTree name :=
  Array.mk (List.range len)

partial def primalSpanningTree (s : SurfaceMesh) : IndexTree `Vertex :=
  go [root] (IndexTree.fullyDisconnected s.vertices.size)
  where
    root : Index `Vertex := s.vertices[0]!.index
    go (worklist: List (Index `Vertex)) (t : IndexTree `Vertex) : IndexTree `Vertex  := Id.run do {
      match worklist with
      | [] => t
      | cur :: rest =>
        let mut t := t;
        let mut worklist := rest; -- we'll be pushing new vertices into worklist.
        for adj in s.getAdjacentVertices cur do {
          if cur == root -- t[cur]! /= cur || cur == root
          then { continue; } -- current vertex is already reached or is root. skip.
          else {
            worklist := adj :: worklist;
            t := t.set! adj cur; -- parent of adj is cur
          }
        };
        go worklist t; -- continue working.
    }

def inPrimalSpanningTree (s : SurfaceMesh) (vertexParent : IndexTree `Vertex) (h : Index `Halfedge) : Bool :=
  let u : Index `Vertex := s.halfedges[h]!.vertex
  let v : Index `Vertex := s.halfedges[s.halfedges[h]!.twin.get!]!.vertex
  vertexParent[u]! == v || vertexParent[v]! == u

def inDualSpanningCotree (s : SurfaceMesh) (faceParent : IndexTree `Face) (h : Index `Halfedge) : Bool :=
   let f : Index `Face := s.halfedges[h]!.face
   let f' : Index `Face := s.halfedges[s.halfedges[h]!.twin.get!]!.face
   faceParent[f]! == f' || faceParent[f']! == f

partial def SurfaceMesh.sharedHalfedge (s : SurfaceMesh) (f g : Index `Face) : Index `Halfedge := Id.run <| do
  for h in s.getAdjacentHalfedges f do
    let twin := s.halfedges[h]!.twin.get!
    let g' := s.halfedges[twin]!.face
    if g' == g
    then return h
    else continue
  panic! "have two faces without adjacent edge!"

partial def dualSpanningCotree (s : SurfaceMesh) (vertexParent : IndexTree `Vertex) : IndexTree `Face :=
  go [root] (IndexTree.fullyDisconnected s.faces.size)
  where
    root : Index `Face := s.faces[0]!.index
    go (worklist: List (Index `Face)) (t : IndexTree `Vertex) : IndexTree `Vertex := Id.run <| do
      match worklist with
      | [] => t
      | cur :: next =>
        let mut t := t;
        let mut worklist := next; -- we'll be pushing new vertices into worklist
        for adjEdge in s.getAdjacentHalfedges cur do {
          -- get the face f the twin of the edge.
          -- This gives us the other face adjacent to the edge.
          let twin := s.halfedges[adjEdge]!.twin.get!
          let face := s.halfedges[twin]!.face
          let adj := face
          if (t[cur]! != cur || cur == root || inPrimalSpanningTree s vertexParent adjEdge)
          then { continue; } -- current vertex is already reached or is root. skip.
          else {
            worklist := adj :: worklist;
            t := t.set! adj cur; -- parent of adj is cur
          }
        }
        go worklist t -- continue working.



/- A homology generator is a sequence of halfedges such that
they are adjacent and form a loop. So:
1. gen[i].vertex == gen[i+1].twin.vertex. (tip of cur = tail of next).
2. gen[gen.size - 1].vertex == gen[0].twin.vertex  (tip of end = tail of start)

Furthermore, this does not lie in the kernel of the boundary operator, so if we take any face,
and add up the oriented halfedges, we would not get this loop.
-/
def HomologyGenerator : Type := Array (Index `Halfedge)


partial def mkGenerator (s : SurfaceMesh)
  (faceParent : IndexTree `Face)
  (h : Index `Halfedge) : HomologyGenerator := Id.run do {
  let h := s.halfedges[h]!;
  let mut f := h.face;
  let mut gens : Array (Index `Halfedge) := #[];
  while faceParent[f]! != f do {
    let parent := faceParent[f]!;
    gens := gens.push (s.sharedHalfedge f parent);
    f := parent;
  }
  let h' := s.halfedges[h.twin.get!]!
  let mut f' := h'.face;
  let mut gens' : Array (Index `Halfedge) := #[];
  while faceParent[f']! != f' do {
    let parent := faceParent[f']!;
    gens := gens.push (s.sharedHalfedge f' parent);
    f' := parent;
  };
  -- find common path. The indeces m, n refer to the prefix
  -- such that f2root[m+1:] === f'2root[n+1:]
  let mut m := gens.size - 1;
  let mut n := gens'.size - 1;
  while gens[m]! == gens'[n]! do {
    if m == 0 || n == 0 then break;
    m := m - 1;
    n := n - 1;
  };
  let mut out := #[h.index];
  for gen in gens[0:m] do {
    out := out.push s.halfedges[gen]!.twin.get!;
  };
  for gen' in gens'[0:n] do {
    out := out.push gen';
  };
  return out;
}

/-- build the homology generators for the given surface. -/
def buildGenerators_ (s : SurfaceMesh)
  (vertexParent : IndexTree `Vertex)
  (faceParent : IndexTree `Face) : Array HomologyGenerator := Id.run do {
  let mut out : Array HomologyGenerator := #[];
  for h in s.halfedges do { 
    if (inPrimalSpanningTree s vertexParent h.index || inDualSpanningCotree s faceParent h.index)
    then { continue }
    else { out := out.push <| mkGenerator s faceParent h.index; }
  }
  return out;
}

/-- Build the homology generators corresponding to a surface mesh. -/
def buildGenerators (s : SurfaceMesh) : Array HomologyGenerator :=
  let vertexParent := primalSpanningTree s
  let faceParent := dualSpanningCotree s vertexParent
  buildGenerators_ s vertexParent faceParent