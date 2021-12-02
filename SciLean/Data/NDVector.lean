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
                 arr := arr.push (f i)
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

  open Enumtype Cont in
  instance {m} [Monad m] 
           [Enumtype ι] [ForIn m (Range ι) (ι × Nat)]
           : ForIn m (NDVector ι) (ℝ × ι × Nat) :=
  {
    forIn := λ v init f => do
      let mut val := init
      for (i,li) in fullRange ι do
        -- Here we are using linear index to acces the container
        -- Not sure if it is worth it ... 
        match (← f (v.lget! li, i, li) val) with
          | ForInStep.done d => return d
          | ForInStep.yield d => val ← d
      pure init
  }
 
end NDVector

abbrev Vector (n : Nat) := NDVector (Fin n)
abbrev Matrix (n m : Nat) := NDVector (Fin n × Fin m)
abbrev RowMatrix (n m : Nat) := NDVector (Fin n × Fin m)
abbrev ColMatrix (n m : Nat) := NDVector (Fin n ×ₗ Fin m)

-- macro 
-- abbrev Tensor3 (n m k : Nat) := NDVector (Fin n × Fin m × Fin k)
-- abbrev Tensor4 (n m k : Nat) := NDVector (Fin n × Fin m × Fin k)


-- TODO: Define tensor with notation `Tensor [n1,n2,n3]`
-- @[reducible]
-- abbrev Tensor.indexOf (l : List Nat) :=
--   match l with
--     | [] => Fin 0
--     | [n] => Fin n
--     | n::ns => Fin n × (indexOf ns)
-- instance (l : List Nat) : Enumtype (Tensor.indexOf l) := HOW TO DO THIS??
-- abbrev Tensor (dims : List Nat) := NDVector (Tensor.indexOf dims)
         

open Cont
open Enumtype

#check IO.Ref

#eval ((do 
  let mut m : Matrix 4 4 := intro λ (i,j) => j.1.toFloat
  
  m := m.lset! 0 42
  IO.println s!"m[0,0] = {m[0,0]}"

  -- This will keep the old version of `m` 
  -- To keep a mutable reference you need to use IO.Ref
  let f := λ i j => m[i,j]

  let ref_m ← IO.mkRef m

  let g : _ → _ → IO _  := λ (i j : Fin 4) => 
  do
    let m' ← ref_m.get
    m'[i,j]
    
  for (i, li) in allIdx m do
    m := set m i (li.toFloat : ℝ) 

  -- I want notation: 
  -- for (a, i, li) in m do
  --   a := f i

  -- !!! This is a trap !!!
  -- It does not change `m`!
  -- for (a, i, li) in m do
  --   m := set m i (li.toFloat : ℝ) 

  IO.println ""

  for (a,i,li) in m do
    IO.println s!"i = {i}  | li = {li}  |  a = {a}  |  f = {f i.1 i.2}  |  g = {← (g i.1 i.2)}"
  

  IO.println ""
) : IO Unit)
