import SciLean.Prelude
import SciLean.Algebra
import SciLean.Mathlib.Data.PowType


def Nat.toInt (n : ℕ) : Int := Int.ofNat n


namespace SciLean

instance : PowType ℤ where
  powType n := {u : Array ℤ // u.size = n}
  intro {n} f := Id.run do
    let mut u : Array ℤ := Array.mkEmpty n
    for i in [0:n] do
      u := u.push (f ⟨i, sorry⟩)
    ⟨u, sorry⟩
  get v i := v.1.get ⟨i, by rw[v.2] apply i.2⟩
  set v i val := ⟨v.1.set ⟨i, by rw[v.2] apply i.2⟩ val, sorry⟩
  ext := sorry

inductive Node (LeafData NodeData : Type) : Type where
| leaf  (data : LeafData) : Node LeafData NodeData
| node  (data : NodeData) (children : Array (Node LeafData NodeData)) : Node LeafData NodeData

namespace VDB_LIKE

  structure GridNode (dim : Nat) (size : Nat) where
    pos : ℤ^dim
    lvl : Nat

  abbrev Index (dim : Nat) (size : Nat) := Fin (size^dim)

  def Index.toPos (idx : Index dim size) : ℤ^dim := Id.run do
    let mut pos : ℤ^dim := 0
    let mut idx := idx.1
    for i in [0:dim] do
      pos[!i] := (idx % size).toInt
      idx := idx / size
    pos
    -- let mask := (2^scl) - 1
    -- PowType.intro λ i => ((idx.1 >>> (i.1 * scl)) &&& mask).toInt

  def toIndex {dim : Nat} (p : ℤ^dim) : Index dim scl :=
    let size := 2^scl
    ⟨∑ i, (p[i].fmod size).toNat <<< (i.1 * scl), sorry⟩
      
  def test : IO Unit := do
    let dim := 2
    let scl := 3
    let N := 2^(dim * scl)
    for i in [0:N] do
      let idx : Index dim scl := ⟨i, sorry⟩
      IO.println s!"{i} {idx.toPos} {((idx.toPos |> toIndex) : Index dim scl)}"

  #eval test

  namespace GridNode

    variable {dim scl : Nat}

    def count (node : GridNode dim scl) := 2^(dim * scl)
    def size  (node : GridNode dim scl) := 2^(scl * node.lvl)
    def originOffset (lvl scl : Nat) : ℤ := ∑ i : Fin (lvl+1), if (i.1 % 2 = 1) then - ((1:ℕ) <<< (i.1 - 1) * scl).toInt else 0

    #eval originOffset 1 2
    def min (node : GridNode dim scl) : ℤ^dim := node.size.toInt * node.pos
    def max (node : GridNode dim scl) : ℤ^dim := node.pos.map (λ x => node.size.toInt * x - 1) -- node.size.toInt * (node.pos + 1) - 1

    def parent (node : GridNode dim scl) : GridNode dim scl := 
      ⟨node.pos.map (λ x => x.fdiv scl), node.lvl+1⟩
    def child  (node : GridNode dim scl) (idx : Index dim scl) : GridNode dim scl := 
      if node.lvl = 0 
      then node
      else ⟨((1:ℕ) <<< scl).toInt * node.pos + idx.toPos, node.lvl-1⟩
    def localPos (node : GridNode dim scl) : ℤ^dim := 
      let size := (1:ℕ) <<< scl
      node.pos.map λ x => x.fmod size
    def index (node : GridNode dim scl) : Index dim scl := 
      node.pos |> toIndex

    -- def node : GridNode 2 2 := ⟨^[-1,0], 0⟩
    -- #eval node.index

    theorem parent_child_index (node : GridNode dim scl) : node.parent.child node.index = node := sorry
    
    def common_index (i j : ℤ) (scl : ℕ) : ℤ×ℕ := Id.run do
      let upper_bound := (Nat.max i.natAbs j.natAbs).log2 + 10
      dbg_trace s!"upper bound := {upper_bound}"
      let mut i := i
      let mut j := j
      let size := (1:ℕ) <<< scl
      for l in [0:upper_bound] do
        if i = j then 
          return (i, l)
        else 
          i := i.fdiv size
          j := j.fdiv size
      panic! "This should be unreachable"

    #eval common_index (8) (-13) 2

    #eval (2^4) - 1
    #check (2^4) - 1

    #eval (2:ℕ).log2 + 1

    -- def min (node : GridNode dim scl) := ((1:ℕ) <<< scl).toInt * pos

  end GridNode


end VDB_LIKE




namespace NewApproach


  structure GridCell (dim size lvl : Nat) where
    pos : ℤ^dim

  namespace GridCell

    def Impl {α} (a : α) := α

    -- Origin of level `lvl+lvlInc` w.r.t. origin of level `lvl`
    -- really not sure if this is correct ...
    -- What is the proper definition ???
    def originOffset (size lvl lvlInc : Nat) : ℤ := 
      if lvl%2 = 0 
      then 
        let e := 2*((lvlInc+1)/2) 
        (1 - (-size.toInt)^e) / (1 + size)       
      else 
        let e := 2*((lvlInc)/2) 
        size*(1 - (-size.toInt)^e) / (1 + size)
  
    theorem originOffset_by_one (size lvl)
      : originOffset size lvl 1 = if lvl%2=0 then 1 - size else 0 := sorry

    def nparent (n : Nat) : GridCell dim size lvl → GridCell dim size (lvl+n) :=
      let offset := originOffset size lvl n
      let nsize := size^n
      λ ⟨p⟩ => ⟨p.map λ xi => (xi - offset).fdiv nsize⟩

    def child (idx : Fin (size^dim)) : GridCell dim size (lvl+1) → GridCell dim size lvl :=
      let offset := originOffset size lvl 1
      let loc_p : ℤ^dim := sorry
      λ ⟨p⟩ => ⟨size.toInt * p + offset * (1:ℤ^dim) + loc_p⟩

    def inParentIdx : GridCell dim size lvl → Fin (size^dim) := sorry
    def inParentPos (node : GridCell dim size lvl) : ℤ^dim := (sorry : Impl $ node.nparent 1 |>.child (!0) |>.pos) 
    -- optimize by
    --   finish_opt
    

    theorem nchild_parentIdx (node : GridCell dim size lvl) : (node.nparent 1).child node.inParentIdx = node := sorry



  end GridCell

  
  #eval  2*((3)/2)

end NewApproach


