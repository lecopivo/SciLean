import SciLean.Prelude
import SciLean.Algebra
import SciLean.Mathlib.Data.PowType


def Array.intro {α} (f : Fin n → α) : Array α := Id.run do
  let mut u : Array α := Array.mkEmpty n
  for i in [0:n] do
    u := u.push (f ⟨i, sorry⟩)
  u

def Array.mkConstant {α} (a : α) (n : Nat) : Array α := Array.intro λ i : Fin n => a

def Nat.toInt (n : ℕ) : Int := Int.ofNat n

def applyNTimes {α} (n : Nat) (f : α → α) (a : α) : α := Id.run do
  match n with
  | 0 => a
  | (n + 1) => applyNTimes n f (f a)

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


namespace Tree

inductive Node (Data : Type) : Type where
| empty : Node Data
| leaf  (data : Data) : Node Data
| node  (children : Array (Node Data)) : Node Data

  namespace Node

  def IsEmpty (node : Node Data) : Prop :=
    match node with
    | .empty => True
    | _ => False

  instance (node : Node Data) : Decidable (node.IsEmpty) := 
    match node with
    | .empty  => isTrue (by simp[IsEmpty] done)
    | .leaf _ => isFalse (by simp[IsEmpty] done)
    | .node _ => isFalse (by simp[IsEmpty] done)

  def IsLeaf (node : Node Data) : Prop :=
    match node with
    | .leaf _ => True
    | _ => False

  instance (node : Node Data) : Decidable (node.IsLeaf) := 
    match node with
    | .leaf _ => isTrue (by simp[IsLeaf] done)
    | .empty  => isFalse (by simp[IsLeaf] done)
    | .node _ => isFalse (by simp[IsLeaf] done)

  inductive Branching (n : Nat) : Node Data → Prop where
    | empty : Branching n empty
    | leaf  : (d : Data) → Branching n (leaf d)
    | node  : {cs : Array (Node Data)} → cs.size = n → (∀ i, Branching n (cs.get i)) → Branching n (node cs)

  -- Leafs are only allowed at a specified depths
  -- The tree also can not exceed the depth
  inductive LeafsAtDepth : Nat → Node Data → Prop where
    | empty (n : Nat) : LeafsAtDepth n empty
    | leaf  : (d : Data) → LeafsAtDepth 0 (leaf d)
    | node  : {cs : Array (Node Data)} → (n : Nat) → (∀ i, LeafsAtDepth n (cs.get i)) → LeafsAtDepth (n+1) (node cs)

  theorem not_a_leaf (node : Node Data) : node.LeafsAtDepth (d+1) → ¬node.IsLeaf := sorry

  end Node

end Tree

/- 
  -- Grid Tree --
  ---------------

  Grid tree is quadtree/octree over integer grid.
-/

namespace Tree
  
  structure GNode (Data : Type) (m d : Nat) where
    node : Node Data
    depth_and_branching : node.Branching m ∧ node.LeafsAtDepth d

  namespace GNode

  -- def IsEmpty (node : GNode Data m d) : Prop := node.1.IsEmpty
  -- instance (node : GNode Data m d) : Decidable (node.IsEmpty) := by simp[IsEmpty]; infer_instance; done

  -- def IsLeaf (node : GNode Data m d) : Prop := node.1.IsLeaf
  -- instance (node : GNode Data m d) : Decidable (node.IsLeaf) := by simp[IsLeaf]; infer_instance; done

  -- def getData {m d} (node : GNode Data m d) (h : node.IsLeaf) : Data :=
  --   match node with
  --   | ⟨.leaf data, _, _⟩ => data

  -- def getData! {m d} (node : GNode Data m d) (default : Data) : Data :=
  --   match node with
  --   | ⟨.leaf data, _, _⟩ => data
  --   | _ => default

  -- def modifyData {m} (node : GNode Data m 0) (f : Data → Data) [Inhabited Data] : GNode Data m 0 :=
  --   match node with
  --   | ⟨.leaf data, _, _⟩ => ⟨.leaf (f data), Node.Branching.leaf (f data), Node.LeafsAtDepth.leaf (f data)⟩
  --   | ⟨.empty, _, _⟩ => ⟨.leaf (f default), Node.Branching.leaf (f default), Node.LeafsAtDepth.leaf (f default)⟩

  -- def setData {m} (node : GNode Data m 0) (data : Data) [Inhabited Data] : GNode Data m 0 :=
  --   node.modifyData (λ _ => data)

  -- def getChild {m d} (node : GNode Data m (d+1)) (i : Fin m) : GNode Data m d :=
  --   match node.1 with
  --   | .node ch => ⟨ch.get ⟨i.1, sorry⟩, sorry⟩
  --   | _ => ⟨.empty, sorry⟩

  -- def modifyChild {m d} (node : GNode Data m (d+1)) (i : Fin m) (f : GNode Data m d → GNode Data m d) : GNode Data m (d+1) :=
  --   match node with
  --   | ⟨.node ch, _, _⟩ => 
  --     let child := f ⟨ch.get ⟨i.1, sorry⟩, sorry⟩
  --     ⟨.node (ch.set ⟨i.1, sorry⟩ child.1), sorry⟩
  --   | ⟨.empty, _, _⟩ => Id.run do
  --     let ch : Array (Node Data) := (Array.mkConstant .empty m)
  --     let child :=  f ⟨.empty, sorry⟩
  --     ⟨.node (ch.set ⟨i.1, sorry⟩ child.1), sorry⟩

  -- def setChild {m d} (node : GNode Data m (d+1)) (i : Fin m) (child : GNode Data m d) : GNode Data m (d+1) :=
  --   node.modifyChild i λ _ => child

  -- Path from a `node : GNode m d` to leaf node
  structure Index (m d : Nat) where
    path : List (Fin m)
    h_len : path.length = d

  instance (m d : Nat) : ToString (Index m d) := ⟨λ i => toString i.1⟩

  def Index.head {m d} (idx : Index m (d+1)) : Fin m := idx.path.head sorry
  def Index.tail {m d} (idx : Index m (d+1)) : Index m d := ⟨idx.path.tail!, sorry⟩

  def getData {m d} (node : GNode Data m d) (idx : Index m d) [Inhabited Data] : Data :=
    match d, node, idx with
    | 0, ⟨.leaf data, _⟩, _ => data
    | 0, ⟨.empty, _⟩, _ => default
    | (d+1), ⟨.empty, _⟩, _ => default
    | (d+1), ⟨.node ch, b, _⟩, ⟨id::ids, h⟩ => 
      let child : GNode Data m d := ⟨ch.get ⟨id, by cases b; rename_i a _; rw[a]; apply id.2;⟩, sorry, sorry⟩
      child.getData ⟨ids, sorry⟩

  def modifyData {m d} (node : GNode Data m d) (idx : Index m d) (f : Data → Data) : GNode Data m d :=
    match d, node, idx with
    |     0, ⟨.leaf data, _⟩, _ => ⟨.leaf (f data), sorry⟩
    |     _,     ⟨.empty, _⟩, _ => ⟨.empty, sorry⟩
    | (d+1),   ⟨.node ch, _⟩, ⟨id::ids, h⟩ => 
      let child : GNode Data m d := ⟨ch.get ⟨id, sorry⟩, sorry⟩
      -- reset `dir` child in the array `ch` to decrement reference counter
      let ch := ch.set ⟨id, sorry⟩ .empty
      -- modify component, hopefully here we do inplace modification
      let child := modifyData child ⟨ids, sorry⟩ f
      ⟨.node (ch.set ⟨id, sorry⟩ child.1), sorry⟩

  def setData {m d} (node : GNode Data m d) (idx : Index m d) (data : Data) : GNode Data m d :=
    match d, node, idx with
    | 0, ⟨.leaf data, _, _⟩, _ => ⟨.leaf data, sorry⟩
    | 0, ⟨.empty, _, _⟩, _ => ⟨.leaf data, sorry⟩
    | (d+1), ⟨.empty, _, _⟩, ⟨id::ids, h⟩ => 
      let child : GNode Data m d := setData ⟨.empty, sorry⟩ ⟨ids, sorry⟩ data
      let ch : Array (Node Data) := Array.mkConstant .empty m
      ⟨.node (ch.set ⟨id, sorry⟩ child.1), sorry⟩
    | (d+1), ⟨.node ch, b, _⟩, ⟨id::ids, h⟩ => 
      let child : GNode Data m d := ⟨ch.get ⟨id, sorry⟩, sorry⟩
      -- reset `dir` child in the array `ch` to decrement reference counter
      let ch := ch.set ⟨id, sorry⟩ .empty
      -- modify component, hopefully here we do inplace modification
      let child := setData child ⟨ids, sorry⟩ data
      ⟨.node (ch.set ⟨id, sorry⟩ child.1), sorry⟩

  def activate {m d} (node : GNode Data m d) (idx : Index m d) [Inhabited Data] : GNode Data m d :=
    node.setData idx default

  def setChild {m d} (node : GNode Data m (d+1)) (i : Fin m) (child : GNode Data m d) : GNode Data m (d+1) :=
    match node with
    | ⟨.empty, _⟩ => 
      let ch : Array (Node Data) := Array.mkConstant .empty m
      ⟨.node (ch.set ⟨i, sorry⟩ child.1), sorry⟩
    | ⟨.node ch, _⟩ => 
      ⟨.node (ch.set ⟨i, sorry⟩ child.1), sorry⟩

  end GNode

end Tree

  -- Represents box with side length `2^depth` and minimal corner `min`
  structure Shape (dim : ℕ) where
    min   : ℤ^dim
    depth : ℕ

  def Shape.size {dim} (ns : Shape dim) : ℕ := (2:ℕ)^(ns.depth)

  def Shape.max {dim} (ns : Shape dim) : ℤ^dim := 
    ns.min + (ns.size-1).toInt * (1:ℤ^dim)

  def Shape.Contains {dim} (ns : Shape dim) (p : ℤ^dim) : Prop :=
    ns.min ≤ p ∧ p ≤ ns.max

  instance {dim} (ns : Shape dim) (p : ℤ^dim) : Decidable (ns.Contains p) :=
    if h : (ns.min ≤ p) ∧ (p ≤ ns.max) then isTrue h else isFalse h

  -- Each box is diveded to 2^dim boxed of half size, they are index with `idx : Fin ((2:ℕ)^dim)`
  -- This function converts this index to directional vector(consisting of 0 and 1) from `min` of a box to `min` of smaller box.
  def Shape.idxToDir {dim : Nat} (idx : Fin ((2:ℕ)^dim)) : ℤ^dim :=
    PowType.intro λ i => ((idx.1 >>> i.1) &&& 1).toInt

  def Shape.child {dim} (s : Shape dim) (idx : Fin ((2:ℕ)^dim)) : Shape dim :=
    if s.depth = 0 then
      s
    else 
      let r := (s.size / 2).toInt
      ⟨s.min + r * idxToDir idx, s.depth - 1⟩
  
  -- Gets a bigger box whose `idx` child is `s`
  def Shape.parent {dim} (s : Shape dim) (idx : Fin ((2:ℕ)^dim)) : Shape dim := 
    ⟨s.min - s.size.toInt * idxToDir idx, s.depth + 1⟩

  -- When we want to create parent that contains point `p`
  -- Gives you (idx, n) telling you that you have to call `parent idx` `n`-times to get a box 
  -- containing `p`
  def Shape.parentIdx {dim : Nat} (s : Shape dim) (p : ℤ^dim) : Fin ((2:ℕ)^dim) × ℕ := Id.run do
    let p := p - s.min
    let mut idx : ℕ := 0
    let mut n : ℕ := 0 
    for i in [0:dim] do
      let i := !i
      if p[i] < 0 then
        idx := idx ||| (1 <<< i.1)
      n := Nat.max n (Nat.log2 ((Int.fdiv (p[i]) s.size).natAbs * 2))
    (!idx, n)

  --- Applying parent `n` times with `idx` given from `parentIdx` ensures that 
  --- point `p` is contained in the resulting box
  theorem Shape.parentIdx_parent {dim} (s : Shape dim) (p : ℤ^dim)
    : let (idx, n) := s.parentIdx p
      let f := λ s' => Shape.parent s' idx
      (applyNTimes n f s).Contains p
    := sorry

  theorem Shape.parentIdx_idxToDir {dim : ℕ} (s : Shape dim) (idx : Fin ((2:ℕ)^dim))
    : (parentIdx s (s.min - idxToDir idx)).1 = idx := sorry

  -- These should hold
  theorem Shape.child_parent {dim} (s : Shape dim) (idx : Fin ((2:ℕ)^dim)) 
    : s.depth ≠ 0 → (s.child idx).parent idx = s :=
  by
    intro h
    simp [parent,child,h,size]
    rw [!?(s.depth - 1 + 1 = s.depth)]
    rw [!?(((2:ℕ)^s.depth) / 2 = (2:ℕ)^(s.depth - 1))]
    -- Now it is obvious
    admit

  theorem Shape.parent_child {dim} (s : Shape dim) (idx : Fin ((2:ℕ)^dim))
    : (s.parent idx).child idx = s := 
  by
    simp [parent,child,size]
    rw [!?(s.depth + 1 - 1 = s.depth)]
    rw [!?(((2:ℕ)^(s.depth + 1)) / 2 = (2:ℕ)^(s.depth))]
    -- Now it is obvious
    admit

  -- Sequence on how to recurse the tree with shape `ns` to reach point `p`
  -- Effectively preforming bit-wise transposition of `p-s.min`
  def Shape.getIndex {dim} (s : Shape dim) (p : ℤ^dim) (h : s.Contains p) 
    : Tree.GNode.Index ((2:ℕ)^dim) s.depth := Id.run do
    let p := p - s.min
    let mut l : List (Fin ((2:ℕ)^dim)) := []
    for i in [0:s.depth] do
      let mut c : Nat := 0
      for j in [0:dim] do
        let pj := p[!j].toNat
        c := c ||| (((pj >>> i) &&& 1) <<< j)
      l := (!c) :: l
    ⟨l,sorry⟩

  def s : Shape 2 := ⟨^[1,-1],2⟩
  
  #eval s.size
  #eval s.min
  #eval s.max
  #eval s.getIndex  ^[4,4] sorry
  #eval s.parentIdx ^[1,7]
  -- example : (Shape.mk ^[(0:ℤ),0] 2).parentIdx ^[(15:ℤ),-13] = (2,2) := by rfl

----------------------------------------------------------------------

  structure GridTree (Data : Type) (dim : Nat) where
    shape : Shape dim
    root  : Tree.GNode Data ((2:ℕ)^dim) shape.depth

  namespace GridTree 

    def Contains {dim} (tree : GridTree Data dim) (p : ℤ^dim) : Prop :=
      tree.shape.Contains p

    instance {dim} (tree : GridTree Data dim) (p : ℤ^dim) : Decidable (tree.Contains p) :=
      by simp[Contains]; infer_instance; done

    def setContained {dim} (tree : GridTree Data dim) (p : ℤ^dim) (data : Data) (h : tree.Contains p) : GridTree Data dim := 
      let idx := tree.shape.getIndex p h
      ⟨tree.shape, tree.root.setData idx data⟩

    -- -- Makes sure that the tree contains p
    def extend {dim} (tree : GridTree Data dim) (p : ℤ^dim) : GridTree Data dim := Id.run do
      let (idx, n) := tree.shape.parentIdx p
      let mut tree := tree
      for i in [0:n] do
        let ⟨shape, root⟩ := tree
        tree := ⟨shape.parent idx, Tree.GNode.setChild ⟨.empty, sorry⟩ idx root⟩
      tree

    theorem extend_Contains  {dim} (tree : GridTree Data dim) (p : ℤ^dim) 
      : (tree.extend p).Contains p := sorry

    def set {dim} (tree : GridTree Data dim) (p : ℤ^dim) (data : Data) : GridTree Data dim := Id.run do
      tree |>.extend p |>.setContained p data (extend_Contains _ _)

    -- {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β
    --- {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (f : Fin as.size → α → m β) : m (Array β)

    def OrderIndependent {dim : ℕ} {Data : Type} {m : Type v → Type w} [Monad m] 
      (f : (ℤ^dim) → Data → m PUnit) : Prop
      := ∀ p p' d d', (do f p d; f p' d') = (do f p' d'; f p d : m PUnit)

    def forIdxM {dim : ℕ} {m : Type v → Type w} [Monad m] 
      (f : (ℤ^dim) → Data → m PUnit) (tree : GridTree Data dim) (h : OrderIndependent f) : m PUnit := sorry

    -- Run over all points in a ball, i.e. for all points `p` such that: `∥p-center∥² ≤ radius2`
    def forBallIdxM {dim : ℕ} {m : Type v → Type w} [Monad m] 
      (f : (ℤ^dim) → Data → m PUnit) (tree : GridTree Data dim) (center : ℤ^dim) (radius2 : ℕ) (h : OrderIndependent f) : m PUnit := sorry

    theorem forBallIdxM_forIdxM {dim : ℕ} {m : Type v → Type w} [Monad m] 
      (f : (ℤ^dim) → Data → m PUnit) (tree : GridTree Data dim) (center : ℤ^dim) (radius2 : ℕ) (h : OrderIndependent f) 
      : (do tree.forBallIdxM f center radius2 h)
        =  
        (do tree.forIdxM 
             (λ p d => 
               if (∑ i, (p[i] - center[i])^2) ≤ radius2 
               then f p d
               else pure PUnit.unit) sorry : m PUnit)
        := sorry

    -- Run over all point in a box, i.e. for all point `p` such that: 
    def forBoxIdxM {dim : ℕ} {m : Type v → Type w} [Monad m] 
      (f : (ℤ^dim) → Data → m PUnit) (tree : GridTree Data dim) (min max : ℤ^dim) (h : OrderIndependent f) : m PUnit := sorry

    theorem forBoxIdxM_forIdxM {dim : ℕ} {m : Type v → Type w} [Monad m] 
      (f : (ℤ^dim) → Data → m PUnit) (tree : GridTree Data dim) (min max : ℤ^dim) (h : OrderIndependent f) 
      : (do tree.forBoxIdxM f min max h)
        =  
        (do tree.forIdxM 
             (λ p d => 
               if (min ≤ p) ∧ (p ≤ max)
               then f p d
               else pure PUnit.unit) sorry : m PUnit)
        := sorry


    -- Somehow run over pairs
    -- How to formulate order independence?  
    -- Probably:
    --    1. Unorder pairs:      (do f p1 d1 p2 d2) = (do f p2 d2 p1 d2)
    --    2. Order independence: (do f p1 d1 p2 d2; f p1' d1' p2' d2') = (do f p1' d1' p2' d2'; f p1 d1 p2 d2)
    -- def forPairsIdxM
    

  end GridTree
    
 -- variable {dim : ℕ} (u v : ℤ^dim)

  -- def set (tree : Tree Data dim) (p : ℤ^dim) (data : Data) : Tree Data dim :=
  --   if tree.root.isEmpty then
  --     ⟨(Node.mkWithEmptyChildren dim), ⟨p, 1⟩⟩
  --   else
  --     let r := (2:ℕ)^depth 
  --     sorry
  -- mutual
  
  -- inductive Node (Data : Type) : (dim : Nat) → (level : Nat) → Type where
  -- | empty (lvl : Nat) : Node Data dim lvl
  -- | node  (lvl : Nat) (children1 : Children Data dim lvl) : Node Data dim (lvl+1)
  -- | leaf  (data : Data) : Node Data dim 0

  -- inductive Children (Data : Type) : (dim : Nat) → (level : Nat) → Type where
  -- | childs {lvl : Nat} (left right : Node Data dim lvl) : Children Data dim lvl
  -- | next   {lvl : Nat} (left right : Children Data d lvl) : Children Data (d+1) lvl
  
  -- end


---------------------------------------------------------------------

