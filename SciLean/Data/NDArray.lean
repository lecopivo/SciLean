import SciLean.Operators
import SciLean.Data.Container

namespace SciLean

structure NDArray (ι : Type u) (α : Type v) [Enumtype ι] where
  (data : Array α)
  (h_size : data.size = numOf ι)

namespace NDArray

  open Enumtype

  variable {α} {ι} [Enumtype ι] (v : NDArray ι α) [Inhabited α]
          
  def lget  (i : Fin (numOf ι)) : α := v.data.get ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ 
  def lget! (i : Nat) : α := v.data.get! i
  def lset  (i : Fin (numOf ι)) (val : α) : NDArray ι α
      := ⟨v.data.set ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ val, sorry⟩
  def lset! (i : Nat) (val : α) : NDArray ι α := ⟨v.data.set! i val, sorry⟩
      
  instance : Cont (NDArray ι α) ι α :=
  {
    toFun := λ v index => v.lget (toFin index)
  }

  variable [ForIn Id (Range ι) (ι × Nat)]

  instance instIntroNDArray : Cont.Intro (NDArray ι α) :=
  {
    intro := λ f => do
               let mut arr := Array.mkEmpty (numOf ι)
               for (i,li) in fullRange ι do
                 arr := arr.push (f i)
               ⟨arr, sorry⟩
    valid := sorry
  }

  -- to get `v.map` notation
  -- TODO: Why do I have to assign the class manually? 
  -- BUD:  I think it might be potentially a bug.
  abbrev intro (f : ι → ℝ) : NDArray ι α := Cont.intro (self := instIntroNDArray) f

  instance : Cont.Set (NDArray ι α) := 
  {
    set := λ v index val => v.lset (toFin index) val
    valid := sorry
  }

  -- to get `v.set` notation
  abbrev set (v : NDArray ι α) (id val) := Cont.set v id val

  instance instMapIdxNDArray : Cont.MapIdx (NDArray ι α) := 
  {
    mapIdx := λ f v₀ => do
                let mut v := v₀
                for (i,li) in fullRange ι do
                  v := v.lset! li (f i (v.lget! li))
                v
    valid := sorry
  }

  -- to get `v.map` notation
  abbrev mapIdx (f : ι → α → α) (v : NDArray ι α) : NDArray ι α := Cont.mapIdx (self := instMapIdxNDArray) f v

  instance : Cont.Map (NDArray ι α) := 
  {
    map := λ f v => mapIdx (λ _ x => f x) v
    valid := sorry
  }

  abbrev map (f : α → α) (v : NDArray ι α) : NDArray ι α := Cont.map (self := instMapNDArray) f v

  open Enumtype Cont in
  instance {m} [Monad m] 
           [Enumtype ι] [ForIn m (Range ι) (ι × Nat)]
           : ForIn m (NDArray ι α) (α × ι × Nat) :=
  {
    forIn := λ v init f => do
      let mut val := init
      for (i,li) in fullRange ι do
        -- Here we are using linear index to acces the container
        -- Not sure if it is worth it ... 
        match (← f (v.lget !li, i, li) val) with
          | ForInStep.done d => return d
          | ForInStep.yield d => val ← d
      pure init
  }
 
end NDArray

-- section Test

--     open NDArray

--     variable {ℝ : Type} [Add ℝ] [Mul ℝ] [Sub ℝ] [Zero ℝ]
--     variable {V : Type → Array Nat → Type} [NDArray V] [HasEMk V]

--     def transpose (A : V ℝ #[n,m]) : V ℝ #[m,n]  := cmk λ i j => A[j,i]
--     def col (A : V ℝ #[n,m]) (j : Fin m) : V ℝ #[n] := cmk λ i => A[i,j]
--     def row (A : V ℝ #[n,m]) (i : Fin n) : V ℝ #[m] := cmk λ j => A[i,j]
--     def mul (A : V ℝ #[n,m]) (B : V ℝ #[m,k]) : V ℝ #[n,k] := cmk (λ i j => ∑ k, A[i,k]*B[k,j])
--     def vec_mul (A : V ℝ #[n,m]) (x : V ℝ #[m]) : V ℝ #[n] := cmk (λ i => ∑ j, A[i,j]*x[j])
--     def abstr (A : V ℝ #[n,m]) := (A[·,·])

--     variable [∀ dims, Inhabited (V ℝ dims)]
--     constant D₂ : (V ℝ #[n,m]) → (V ℝ #[n,m,4])
--     constant D₃ : (V ℝ #[n,m,k]) → (V ℝ #[n,m,k,4])

--     -- General Relativity formulas
--     -- https://en.wikipedia.org/wiki/List_of_formulas_in_Riemannian_geometry

--     variable (g : V ℝ #[4,4])

--     def Γ₁ : V ℝ #[4,4,4] := cmk λ c a b => (D₂ g)[c,a,b] + (D₂ g)[c,b,a] - (D₂ g)[a,b,c]
--     def Γ₂ : V ℝ #[4,4,4] := cmk λ k i j => ∑ l, g[k,l]*(Γ₁ g)[l,i,j]
--     def R  : V ℝ #[4,4,4,4] := cmk λ i j k l => let Γ := Γ₂ g
--                                             (D₃ Γ)[l,i,k,j] + (D₃ Γ)[l,j,k,i] + ∑ p, (Γ[p,i,k] * Γ[l,j,p] - Γ[p,j,k] - Γ[l,i,p])
--     def 𝓡  : V ℝ #[4,4] := cmk λ i k => ∑ j, (R g)[i,j,k,j]
--     def SR : ℝ := ∑ i k, g[i,k] * (𝓡 g)[i,k]
--     def G  : V ℝ #[4,4] := cmk λ i k => (𝓡 g)[i,k] - (SR g) * g[i,k]

-- end Test
