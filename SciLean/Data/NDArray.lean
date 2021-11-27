
-- Some auxiliary definitions
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

namespace NDArray

  def Index (dims : Array Nat) := (d : Fin dims.size) → Fin (dims[d])

end NDArray

--- Type A is a NDArray with densions dims and value type T
class NDArray (A : Type u) (T : Type v) (dims : Array Nat)  where 
  elem : A → NDArray.Index dims → T     -- get and element
  emk : (NDArray.Index dims → T) → A   -- elementa wise make

--- Automatically infering T and dims based on A
class NDArrayData (A : Type u) where
  T : Type v
  dims : Array Nat

-- Is this good idea?
@[reducible] 
instance (A : Type u) (T : Type v) (dims : Array Nat) [NDArray A T dims] : NDArrayData A := ⟨T, dims⟩

attribute [reducible, inline] NDArrayData.T NDArrayData.dims

namespace NDArray

  namespace Index

    def toIndex1 (i1 : Fin n1) : Index #[n1] 
    | Fin.mk 0 _ => i1

    def toIndex2 (i1 : Fin n1) (i2 : Fin n2) : Index #[n1, n2] 
    | Fin.mk 0 _ => i1
    | Fin.mk 1 _ => i2

    def toIndex3 (i1 : Fin n1) (i2 : Fin n2) (i3 : Fin n3) : Index #[n1, n2, n3] 
    | Fin.mk 0 _ => i1
    | Fin.mk 1 _ => i2
    | Fin.mk 2 _ => i3

    def toIndex4 (i1 : Fin n1) (i2 : Fin n2) (i3 : Fin n3) (i4 : Fin n4) : Index #[n1, n2, n3, n4] 
    | Fin.mk 0 _ => i1
    | Fin.mk 1 _ => i2
    | Fin.mk 2 _ => i3
    | Fin.mk 3 _ => i4

    -- How to generalize?

  end Index

  @[reducible]
  abbrev scalarOf {A} (a : A) [NDArrayData A] := NDArrayData.T A

  @[reducible]
  abbrev dimsOf {A} (a : A) [NDArrayData A] := NDArrayData.dims A

  @[reducible]
  abbrev get {A} [NDArrayData A] [NDArray A (NDArrayData.T A) (NDArrayData.dims A)] (a : A) := @elem _ (scalarOf a) (dimsOf a) _ a

  -- macro a:term noWs "[[" i:term "]]" : term =>
  --   `(elem (T := scalarOf $a) (dims := dimsOf $a) $a $i)
  
  -- This can be turned into one macro once we have general toIndexₙ
  macro a:term noWs "[" i1:term "]" : term =>
    `(elem (T := scalarOf $a) (dims := dimsOf $a) $a (Index.toIndex1 $i1))

  macro a:term noWs "[" i1:term "," i2:term "]" : term =>
    `(elem (T := scalarOf $a) (dims := dimsOf $a) $a (Index.toIndex2 $i1 $i2))

  macro a:term noWs "[" i1:term "," i2:term "," i3:term "]" : term =>
    `(elem (T := scalarOf $a) (dims := dimsOf $a) $a (Index.toIndex3 $i1 $i2 $i3))

  macro a:term noWs "[" i1:term "," i2:term "," i3:term "," i4:term "]" : term =>
    `(elem (T := scalarOf $a) (dims := dimsOf $a) $a (Index.toIndex4 $i1 $i2 $i3 $i4))

  
  -- Make NDArray from an arbitrary type
  -- Mainly used to create an array from lambdas like (λ i j k => f i j k)
  section CustomMk
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
    instance [NDArray A T #[n1, n2, n3, n4]] : CustomMk A (Fin n1 → Fin n2 → Fin n3 → Fin n4 → T) := 
             ⟨λ f => NDArray.emk (λ i : Index #[n1, n2, n3, n4] => f (i ⟨0, by simp[Array.size, List.length] done⟩) 
                                                                     (i ⟨1, by simp[Array.size, List.length] done⟩) 
                                                                     (i ⟨2, by simp[Array.size, List.length] done⟩)
                                                                     (i ⟨3, by simp[Array.size, List.length] done⟩))⟩
    --- ... and so on ...
  
    def cmk [CustomMk A α] (a : α) : A := CustomMk.customMk a

  end CustomMk


  section Operations

    class HasMap {T dims} (A : Type u) [NDArray A T dims] where
      map : (T → T) → (A → A)
      is_map : ∀ (f : T → T) (a : A) i, (f (get a i) = get (map f a) i)

    class HasMap₂ (A : Type u) (T : Type v) where
      map₂ : (T → T) → (A → A → A)

  end Operations

end NDArray

section Test

    open NDArray

    constant ℝ : Type
    instance : Add ℝ := sorry
    instance : Mul ℝ := sorry
    instance : Sub ℝ := sorry
    instance : Zero ℝ := sorry
    constant V1 : Type
    constant V2 : Type
    constant V3 : Type
    constant V4 : Type
    instance : NDArray V1 ℝ #[4] := sorry
    instance : NDArray V2 ℝ #[4,4] := sorry
    instance : NDArray V3 ℝ #[4,4,4] := sorry
    instance : NDArray V4 ℝ #[4,4,4,4] := sorry

    def transpose (A : V2) : V2       := cmk λ i j => A[j,i]
    def col (A : V2) (j : Fin 4) : V1 := cmk λ i => A[i,j]
    def row (A : V2) (i : Fin 4) : V1 := cmk λ j => A[i,j]
    def trace (A : V2) : ℝ            := ∑ i, A[i,i]
    def mul (A B : V2) : V2           := cmk (λ i j => ∑ k, A[i,k]*B[k,j])

    variable [Inhabited V2] [Inhabited V3] [Inhabited V4]
    constant D₁ : V1 → V2
    constant D₂ : V2 → V3 
    constant D₃ : V3 → V4

    -- General Relativity formulas
    -- https://en.wikipedia.org/wiki/List_of_formulas_in_Riemannian_geometry

    def Γ₁ (g : V2) : V3 := cmk λ c a b => (D₂ g)[c,a,b] + (D₂ g)[c,b,a] - (D₂ g)[a,b,c]
    def Γ₂ (g : V2) : V3 := cmk λ k i j => ∑ l, g[k,l]*(Γ₁ g)[l,i,j]
    def R (g : V2) : V4 := cmk λ i j k l => let Γ : V3 := Γ₂ g
                                            (D₃ Γ)[l,i,k,j] + (D₃ Γ)[l,j,k,i] + ∑ p, (Γ[p,i,k] * Γ[l,j,p] - Γ[p,j,k] - Γ[l,i,p])
    def 𝓡 (g : V2) : V2 := cmk λ i k => ∑ j, (R g)[i,j,k,j]
    def SR (g : V2) : ℝ := ∑ i k, g[i,k] * (𝓡 g)[i,k]
    def G (g : V2) : V2 := cmk λ i k => (𝓡 g)[i,k] - (SR g) * g[i,k]

end Test

