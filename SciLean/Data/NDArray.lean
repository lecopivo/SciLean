import SciLean.Algebra

-- Some auxiliary definitions
namespace NDArray

  def Index (dims : Array Nat) := (d : Fin dims.size) → Fin (dims[d])

end NDArray

-- Do I want to have rank as explicit argument of `A` ?? 
--- Type A is a NDArray with densions dims and value type T
class NDArray (A : Type v → Array Nat → Type u) where 
  get {T dims} : A T dims → NDArray.Index dims → T     -- get and element
  -- emk {T dims} : (NDArray.Index dims → T) → A T dims   -- element wise make

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

  -- This can be turned into one macro once we have general toIndexₙ
  macro a:term noWs "[" i1:term "]" : term =>
    `(get $a (Index.toIndex1 $i1))

  macro a:term noWs "[" i1:term "," i2:term "]" : term =>
    `(get $a (Index.toIndex2 $i1 $i2))

  macro a:term noWs "[" i1:term "," i2:term "," i3:term "]" : term =>
    `(get $a (Index.toIndex3 $i1 $i2 $i3))

  macro a:term noWs "[" i1:term "," i2:term "," i3:term "," i4:term "]" : term =>
    `(get $a (Index.toIndex4 $i1 $i2 $i3 $i4))
  
  -- Make NDArray from an arbitrary type
  -- Mainly used to create an array from lambdas like (λ i j k => f i j k)

  section Operations

    -- Has map for function satisfying predicate P. 
    -- This is mainly usefull for sparse matrices requiring (∀ i, (f i 0) = 0)
    -- i.e. pmap is not allowed to change the sparsity pattern
    class HasPMapIdx (A T) (P : {dims : Array Nat} → (Index dims → T → T) → Prop) [NDArray A] where
      pmap {dims} : (f : Index dims → T → T) → (P f) → (A T dims → A T dims)
      is_pmap {dims} : ∀ (f : Index dims → T → T) (h : P f) (a : A T dims) i, (f i (get a i) = get (pmap f h a) i)

    class HasMapIdx (A T) [NDArray A] extends HasPMapIdx A T (λ _ => True)

    def mapIdx {A T dims} [NDArray A] [HasMapIdx A T] 
               (f : Index dims → T → T) (a : A T dims) : A T dims
               := HasPMapIdx.pmap (P := (λ _ => True)) f True.intro a

    @[inline]
    def map {A T dims} [NDArray A] [HasMapIdx A T] 
            (f : T → T) (a : A T dims) : A T dims
            := mapIdx (λ _ => f) a

    -- Map that preserves zeroes, usefull for sparse matrices
    class HasZMapIdx (A T) [Zero T] [NDArray A] extends HasPMapIdx A T (λ f => ∀ i, f i 0 = (0 : T))
    def zmapIdx {A T dims} [Zero T] [NDArray A] [HasZMapIdx A T] 
                (f : Index dims → T → T) (h : ∀ i, f i 0 = (0 : T)) (a : A T dims) : A T dims
                := HasPMapIdx.pmap (P := (λ f => ∀ i, f i 0 = (0 : T))) f h a


    class HasEMk (A) [NDArray A] where
      emk {T dims} : (Index dims → T) → A T dims   -- element wise make
      is_emk {T dims} : ∀ (f : Index dims → T) i, get (emk f) i = f i

    def emk {A T dims} [NDArray A] [HasEMk A] : (Index dims → T) → A T dims := HasEMk.emk

  end Operations


  section CustomMk
    class CustomMk (α : Type w) (A : Type v → Array Nat → Type u) (T dims) where customMk : α → A T dims

    variable {A T} [NDArray A] [HasEMk A]
    instance : CustomMk (Fin n → T) A T #[n] :=
             ⟨λ f => emk (λ i : Index #[n] => f (i ⟨0, by simp[Array.size, List.length] done⟩))⟩
    instance : CustomMk (Fin n1 → Fin n2 → T) A T #[n1,n2] := 
             ⟨λ f => emk (λ i : Index #[n1, n2] => f (i ⟨0, by simp[Array.size, List.length] done⟩) 
                                                             (i ⟨1, by simp[Array.size, List.length] done⟩))⟩
    instance : CustomMk (Fin n1 → Fin n2 → Fin n3 → T) A T #[n1,n2,n3] := 
             ⟨λ f => emk (λ i : Index #[n1, n2, n3] => f (i ⟨0, by simp[Array.size, List.length] done⟩) 
                                                                 (i ⟨1, by simp[Array.size, List.length] done⟩) 
                                                                 (i ⟨2, by simp[Array.size, List.length] done⟩))⟩
    instance : CustomMk (Fin n1 → Fin n2 → Fin n3 → Fin n4 → T) A T #[n1,n2,n3,n4] := 
             ⟨λ f => emk (λ i : Index #[n1, n2, n3, n4] => f (i ⟨0, by simp[Array.size, List.length] done⟩) 
                                                                     (i ⟨1, by simp[Array.size, List.length] done⟩) 
                                                                     (i ⟨2, by simp[Array.size, List.length] done⟩)
                                                                     (i ⟨3, by simp[Array.size, List.length] done⟩))⟩

    --- ... and so on ...
  
    def cmk {α A T dims} [CustomMk α A T dims] (a : α) : A T dims := CustomMk.customMk a

  end CustomMk


end NDArray

section Test

    open NDArray

    variable {ℝ : Type} [Add ℝ] [Mul ℝ] [Sub ℝ] [Zero ℝ]
    variable {V : Type → Array Nat → Type} [NDArray V] [HasEMk V]

    def transpose (A : V ℝ #[n,m]) : V ℝ #[m,n]  := cmk λ i j => A[j,i]
    def col (A : V ℝ #[n,m]) (j : Fin m) : V ℝ #[n] := cmk λ i => A[i,j]
    def row (A : V ℝ #[n,m]) (i : Fin n) : V ℝ #[m] := cmk λ j => A[i,j]
    def mul (A : V ℝ #[n,m]) (B : V ℝ #[m,k]) : V ℝ #[n,k] := cmk (λ i j => ∑ k, A[i,k]*B[k,j])
    def vec_mul (A : V ℝ #[n,m]) (x : V ℝ #[m]) : V ℝ #[n] := cmk (λ i => ∑ j, A[i,j]*x[j])
    def abstr (A : V ℝ #[n,m]) := (A[·,·])

    variable [∀ dims, Inhabited (V ℝ dims)]
    constant D₂ : (V ℝ #[n,m]) → (V ℝ #[n,m,4])
    constant D₃ : (V ℝ #[n,m,k]) → (V ℝ #[n,m,k,4])

    -- General Relativity formulas
    -- https://en.wikipedia.org/wiki/List_of_formulas_in_Riemannian_geometry

    variable (g : V ℝ #[4,4])

    def Γ₁ : V ℝ #[4,4,4] := cmk λ c a b => (D₂ g)[c,a,b] + (D₂ g)[c,b,a] - (D₂ g)[a,b,c]
    def Γ₂ : V ℝ #[4,4,4] := cmk λ k i j => ∑ l, g[k,l]*(Γ₁ g)[l,i,j]
    def R  : V ℝ #[4,4,4,4] := cmk λ i j k l => let Γ := Γ₂ g
                                            (D₃ Γ)[l,i,k,j] + (D₃ Γ)[l,j,k,i] + ∑ p, (Γ[p,i,k] * Γ[l,j,p] - Γ[p,j,k] - Γ[l,i,p])
    def 𝓡  : V ℝ #[4,4] := cmk λ i k => ∑ j, (R g)[i,j,k,j]
    def SR : ℝ := ∑ i k, g[i,k] * (𝓡 g)[i,k]
    def G  : V ℝ #[4,4] := cmk λ i k => (𝓡 g)[i,k] - (SR g) * g[i,k]

end Test
