import SciLean.Operators
import SciLean.Data.Container

namespace SciLean

structure NDVector (ι : Type u) [Enumtype ι] where
  (data : FloatArray)
  (h_size : data.size = numOf ι)

namespace NDVector

  open Enumtype

  variable {ι} [Enumtype ι] (v : NDVector ι)
          
  def lget  (i : Fin (numOf ι)) : ℝ := v.data.get ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ 
  def lget! (i : Nat) : ℝ := v.data.get! i
  def lset  (i : Fin (numOf ι)) (val : ℝ) : NDVector ι
      := ⟨v.data.set ⟨i.1, by rw [v.h_size]; apply i.2; done⟩ val, sorry⟩
  def lset! (i : Nat) (val : ℝ) : NDVector ι := ⟨v.data.set! i val, sorry⟩
      
  instance : Cont (NDVector ι) ι ℝ :=
  {
    toFun := λ v index => v.lget (toFin index)
  }

  variable [ForIn Id (Range ι) (ι × Nat)]

  instance instIntroNDVector : Cont.Intro (NDVector ι) :=
  {
    intro := λ f => do
               let mut arr := FloatArray.mkEmpty (numOf ι)
               for (i,li) in fullRange ι do
                 arr := arr.set! li (f i)
               ⟨arr, sorry⟩
    valid := sorry
  }

  -- to get `v.map` notation
  -- TODO: Why do I have to assign the class manually? 
  -- BUD:  I think it might be potentially a bug.
  abbrev intro (f : ι → ℝ) : NDVector ι := Cont.intro (self := instIntroNDVector) f

  instance : Cont.Set (NDVector ι) := 
  {
    set := λ v index val => v.lset (toFin index) val
    valid := sorry
  }

  -- to get `v.set` notation
  abbrev set (v : NDVector ι) (id val) := Cont.set v id val

  instance instMapIdxNDVector : Cont.MapIdx (NDVector ι) := 
  {
    mapIdx := λ f v₀ => do
                let mut v := v₀
                for (i,li) in fullRange ι do
                  v := v.lset! li (f i (v.lget! li))
                v
    valid := sorry
  }

  -- to get `v.map` notation
  abbrev mapIdx (f : ι → ℝ → ℝ) (v : NDVector ι) : NDVector ι := Cont.mapIdx (self := instMapIdxNDVector) f v

  instance : Cont.Map (NDVector ι) := 
  {
    map := λ f v => mapIdx (λ _ x => f x) v
    valid := sorry
  }

  abbrev map (f : ℝ → ℝ) (v : NDVector ι) : NDVector ι := Cont.map (self := instMapNDVector) f v


end NDVector


