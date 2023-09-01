/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

Tree Cotree algorithm to compute homology generators.
https://github.com/GeometryCollective/geometry-processing-js/blob/c7ea47ae808979a5361e3fcd61bf921a194bf897/projects/vector-field-decomposition/tree-cotree.js
[1] Greedy optimal homotopy and homology generators
-/

import SciLean.Modules.DDG.SurfaceMesh

abbrev Tree (name : Name) := Array (Index name) -- array of parent pointers

def Tree.fullyDisconnected (len : Nat) : Tree name where
  vertexParent := Array.fromList (List.range 0 len)

def primalSpanningTree (s : SurfaceMesh) : Tree `Vertex :=
  go [root] (Tree.fullyDisconnected (len s.vertices))
  where
    root : Index `Vertex := s.vertices[0]!
    go (worklist: List (Index `Vertex)) (t : Tree) : Tree  := Id.run do
      match worklist with
      | [] => t
      | cur :: next =>
        let mut t := t
        let mut worklist := next -- we'll be pushing new vertices into worklist
        for adj in t.getAdjacentVertices cur do
          if t[cur] /= cur || cur == root
          then continue -- current vertex is already reached or is root. skip.
          else
            worklist := adj :: worklist
            t := t.set! adj cur -- parent of adj is cur
        go worklist t -- continue working.

def inPrimalSpanningTree (s : SurfaceMesh) (vertexParents : Tree `Vertex) (h : Index `Halfedge) : Bool :=
  let u := h.vertex
  let v := s.twin h.vertex
  vertexParents[u] == v || vertexParents[v] == u

def in DualSpanningCotree (s : SurfaceMesh) (faceParent : Tree `Face) (h : Index `Halfedge) : Bool :=
   let f := h.face
   let f' := h.twin.face
   faceParent[f] == f' || faceParent[f'] == f

def sharedHalfedge (s : SurfaceMesh (f g : Index `Face) : Halfedge := Id.run
  for h in s.getAdjacentHalfedges f do
    if s.face (s.twin h) == g
    then return h
  panic! "have two faces without adjacent edge!"

def dualSpanningCotree (s : SurfaceMesh) (vertexParents : Tree `Vertex) : Tree `Face :=
  go [root] (Tree.fullyDisconnected (len s.faces))
  where
    root : Index `Vertex := s.faces[0]!
    go (worklist: List (Index `Face)) (t : Tree) : Tree  := Id.run do
      match worklist with
      | [] => t
      | cur :: next =>
        let mut t := t
        let mut worklist := next -- we'll be pushing new vertices into worklist
        for adjEdge in t.getAdjacentHalfedges cur do
          -- get the face f the twin of the edge.
          -- This gives us the other face adjacent to the edge.
          let adj := s.getFace (s.getTwin adjEdge)
          if t[cur] /= cur || cur == root || inPrimalSpanningTree vertexParents adjEdge
          then continue -- current vertex is already reached or is root. skip.
          else
            worklist := adj :: worklist
            t := t.set! adj cur -- parent of adj is cur
        go worklist t -- continue working.


def Tree.pathFromTo (t : Tree name) (v w : Vertex) := do
  let p1 := -- get path to

def HomologyGenerator : Type := Array (Index `Halfedge)
/-- build the homology generators for the given surface. -/
def buildGenerators_ (s : SurfaceMesh)
  (vertexParents : Tree `Vertex)
  (faceParents : Tree `Face) : Array HomologyGenerator := Id.run do
  for e in s.edges do
   if inPrimalSpanningTree vertexParents e || inDualSpanningCotree faceParents e
   then continue
