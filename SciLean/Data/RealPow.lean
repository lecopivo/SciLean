import SciLean.Data.PowType

namespace SciLean

structure NFloatArray (n : ℕ) where
  data : FloatArray
  h_size : data.size = n

structure RealArray where
  data : FloatArray

namespace RealArray 

  def size (u : RealArray) : Nat := u.data.size

  def get (u : RealArray) (i : Fin u.size) : ℝ := ⟨u.data.get !i.1⟩
  def set (u : RealArray) (i : Fin u.size) (x : ℝ) : RealArray := ⟨u.data.set (!i.1) (x.1)⟩

  def intro {n} (f : Fin n → ℝ) : RealArray := Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in [0:n] do
      let i := ⟨i, sorry⟩
      x := x.push (f i).val
    ⟨x⟩

end RealArray


structure NRealArray (n : ℕ) where
  data : RealArray
  h_size : data.size = n

namespace NRealArray

  def get {n} (u : NRealArray n) (i : Fin n) : ℝ := u.1.get !i.1
  def set {n} (u : NRealArray n) (i : Fin n) (x : ℝ) : NRealArray n := ⟨u.1.set (!i.1) x, sorry⟩
  def intro {n} (f : Fin n → ℝ) : NRealArray n := ⟨RealArray.intro f, sorry⟩

end NRealArray


instance : PowType ℝ := 
{
  powType := λ n => NRealArray n -- NFloatArray n -- {a : FloatArray // a.size = n}
  intro := NRealArray.intro 
  get := NRealArray.get
  set := NRealArray.set
  ext := sorry
}

instance (m : Nat) : PowType (ℝ^m) := 
{
  powType := λ n => NFloatArray n -- {a : FloatArray // a.size = n * m}
  intro := λ {n} f => Id.run do
    let mut x := FloatArray.mkEmpty (n*m)
    for i in [0:n] do
      let xi := (f !i)
      for j in [0:m] do
        x := x.push (xi[!j]).val
    !x
  get := λ x i => 
    PowType.intro λ j => ⟨x.1.get !(i.1*m + j.1)⟩
  set := λ x i xi => Id.run do
    let mut x := x.1
    let offset := i.1*m
    for j in [0:m] do
      x := x.set (!(j + offset)) (xi[!j]).val
    !x
  ext := sorry
}
