
class Zero (α : Type u) where
  zero : α

instance instOfNatZero [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

def sum {n α} [Zero α] [Add α] (f : Fin n → α) : α := do
  let mut r := 0
  for i in [0:n] do
    r := r + f ⟨i, sorry⟩
  r

macro "∑" xs:Lean.explicitBinders ", " b:term : term => Lean.expandExplicitBinders `sum xs b

def Array.product (l : Array Nat) : Nat := do
  let mut prod := 1
  for i in [0:l.size] do
    prod := prod * l[i]
  prod

namespace NDArray

  def Index (dims : Array Nat) := (d : Fin dims.size) → Fin (dims[d])

end NDArray

--- Type A is a NDArray with densions dims and value type T
class NDArray (A : Type u) (T : Type v) (dims : Array Nat)  where 
  get : A → NDArray.Index dims → T     -- get and element
  emk : (NDArray.Index dims → T) → A   -- elementa wise make

--- Automatically infering T and dims based on A
class NDArrayData (A : Type u) where
  T : Type v
  dims : Array Nat

-- Is this good idea?
instance (A : Type u) (T : Type v) (dims : Array Nat) [NDArray A T dims] : NDArrayData A := ⟨T, dims⟩

attribute [reducible, inline] NDArrayData.T NDArrayData.dims

namespace NDArray

  -- variable {A : Type u} {T : Type v} {dims : Array Nat}
  -- variable [NDArray A]

  namespace Index

    variable {dims : Array Nat}

    -- TODO
    -- https://en.wikipedia.org/wiki/Row-_and_column-major_order#Address_calculation_in_general
    def toRowLinear : Index dims → Fin dims.product := sorry -- i_n + N_{n} * (i_{n-1} + ...)
    def toColLinear : Index dims → Fin dims.product := sorry -- i1 + N1 * (i2 + ...)
    def fromRowLinear (dims : Array Nat) (i : Fin dims.product) : Index dims := sorry
    def fromColLinear (dims : Array Nat) (i : Fin dims.product) : Index dims := sorry

    def toIndex1 (i1 : Fin n1) : Index #[n1] 
    | Fin.mk 0 _ => i1

    def toIndex2 (i1 : Fin n1) (i2 : Fin n2) : Index #[n1, n2] 
    | Fin.mk 0 _ => i1
    | Fin.mk 1 _ => i2

    def toIndex3 (i1 : Fin n1) (i2 : Fin n2) (i3 : Fin n3) : Index #[n1, n2, n3] 
    | Fin.mk 0 _ => i1
    | Fin.mk 1 _ => i2
    | Fin.mk 2 _ => i3

    -- How to generalize?

  end Index

  section CommonNDArrays

    variable {α : Type} 

    instance : NDArray (Fin n → α) α #[n] :=
    {
      get := λ f index => f (index ⟨0, by simp[Array.size, List.length] done⟩)
      emk := λ f i => f (Index.toIndex1 i)
    }

    instance : NDArrayData (Fin n → α) :=
    {
      T := α
      dims := #[n]
    }
    
    instance : NDArray (Fin n1 → Fin n2 → α) α #[n1,n2] :=
    {
      get := λ f index => f (index ⟨0, by simp[Array.size, List.length] done⟩)
                            (index ⟨1, by simp[Array.size, List.length] done⟩)
      emk := λ f i1 i2 => f (Index.toIndex2 i1 i2)
    }

    instance : NDArrayData (Fin n1 → Fin n2 → α) :=
    {
      T := α
      dims := #[n1,n2]
    }
  
    instance : NDArray (Fin n1 → Fin n2 → Fin n3 → α) α #[n1,n2,n3] :=
    {
      get := λ f index => f (index ⟨0, by simp[Array.size, List.length] done⟩)
                            (index ⟨1, by simp[Array.size, List.length] done⟩)
                            (index ⟨2, by simp[Array.size, List.length] done⟩)
      emk := λ f i1 i2 i3 => f (Index.toIndex3 i1 i2 i3)
    }

    instance : NDArrayData (Fin n1 → Fin n2 → Fin n3 → α) :=
    {
      T := α
      dims := #[n1, n2, n3]
    }
  
  end CommonNDArrays

  @[reducible]
  abbrev scalarOf {A} (a : A) [NDArrayData A] := NDArrayData.T A

  @[reducible]
  abbrev dimsOf {A} (a : A) [NDArrayData A] := NDArrayData.dims A

  macro a:term noWs "[" i1:term "]" : term =>
    `(@NDArray.get _ (scalarOf $a) (dimsOf $a) _ $a (Index.toIndex1 $i1))

  macro a:term noWs "[" i1:term "," i2:term "]" : term =>
    `(@NDArray.get _ (scalarOf $a) (dimsOf $a) _ $a (Index.toIndex2 $i1 $i2))

  macro a:term noWs "[" i1:term "," i2:term "," i3:term "]" : term =>
    `(@NDArray.get _ (scalarOf $a) (dimsOf $a) _ $a (Index.toIndex3 $i1 $i2 $i3))

  -- how to generalize?
  
  section CustomMk
    -- Make NDArray from an arbitrary type - mainly used to create from lambdas like (λ i j k => f i j k)
    class CustomMk (A : Type u) (α : Type w) where customMk : α → A

    variable {A : Type u} {T : Type v}
  
    instance [NDArray A T #[n]] : CustomMk A (Fin n → T) :=
             ⟨λ f => NDArray.emk (λ i : Index #[n] => f (i ⟨0, by simp[Array.size, List.length] done⟩))⟩
    instance [NDArray A T #[n1, n2]] : CustomMk A (Fin n1 → Fin n2 → T) := 
             ⟨λ f => NDArray.emk (λ i : Index #[n1, n2] => f (i ⟨0, by simp[Array.size, List.length] done⟩) 
                                                             (i ⟨1, by simp[Array.size, List.length] done⟩))⟩
    instance [NDArray A T #[n1, n2, n3]] : CustomMk A (Fin n1 → Fin n2 → Fin n3 → T) := 
             ⟨λ f => NDArray.emk (λ i : Index #[n1, n2, n3] => f (i ⟨0, by simp[Array.size, List.length] done⟩) 
                                                                 (i ⟨1, by simp[Array.size, List.length] done⟩) 
                                                                 (i ⟨2, by simp[Array.size, List.length] done⟩))⟩
    --- ... and so on ...
  
    def cmk [CustomMk A α] (a : α) : A := CustomMk.customMk a

  end CustomMk

  -- section Operations

  --   constant T' : Type
  --   constant B : Type
  --   constant C : Type
  --   variable  {dims : Array Nat}
  --   instance asdf : HasElements B := ⟨T'⟩

  --   #check asdf

  --   variable [NDArray A T dims] [NDArray B T dims] [NDArray C T dims]

  --   variable (a : A) (id : Index dims)

  --   instance [Add T] : Add A := ⟨λ a b => ((NDArray.emk λ (id : Index dims) => ((NDArray.get a id) + (NDArray.get b id) : T)))⟩

  --   section Mul

  --   variable [Add T] [Mul T] [Zero T] [NDArray A T #[n,k]] [NDArray B T #[k,m]] [NDArray C T #[n,m]]
  --   variable (a : A) (b : B) (c : C) (i : Fin n) (j : Fin m) (l : Fin k)
    

  --   #check HasElements.elementType

  --   set_option trace.Meta.synthInstance true in
  --   #check (HasElements.elementType B)

  --   -- #check b[i,l]

  --   -- #check (λ (i : Fin n) (j : Fin m) => ∑ l, (a[i,l] * b[l,j] : T))

  --   -- instance [Add T] [Mul T] [NDArray A T #[n,m]] [NDArray B T #[k,m]] [NDArray C T #[n,m]] : HMul A B C := 
  --   --          ⟨λ a b => ((NDArray.cmk λ i j => ∑ l, a[i,l]*b[l,j]))⟩

  --   end Mul

  --   #check Nat

  -- end Operations


end NDArray

section Test

    -- constant A : Type
    -- constant B : Type
    -- constant T : Type
    -- def n := 9
    -- def m := 10
    -- def k := 11

    variable {n m k : Nat}
    variable (T : Type) [Add T] [Mul T] [Zero T]
    variable (A : Type) [NDArray A T #[n,k]]
    variable (B : Type) [NDArray B T #[k,m]]
    variable (C : Type) [NDArray C T #[n,m]]
    variable (D : Type) [NDArray D T #[n,n]]
    variable (a : A) (b : B) (d : D) (i : Fin n) (j : Fin m) (l : Fin k)

    #check ((NDArray.cmk (λ i j => ∑ l, a[i,l] * b[l,j])) : C) -- create a*b with C type storage
    #check λ j => a[i,j]
    #check (a[i,·])
    #check (a[·,·])
    #check (a[·,l])
    #check (λ i => d[i,i])

end Test
