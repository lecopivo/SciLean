import SciLean.Data.PowType

namespace SciLean

instance (n : Nat) : PowType ℝ n := 
{
  powType := {a : FloatArray // a.size = n}
  intro := λ f => Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in [0:n] do
      let i := ⟨i, sorry⟩
      x := x.push (f i).val
    ⟨x, sorry⟩
  get := λ x i => ⟨x.1.get ⟨i.1, sorry⟩⟩
  set := λ x i xi => ⟨x.1.set ⟨i.1, sorry⟩ xi.val, sorry⟩
  ext := sorry
}

instance (n m : Nat) : PowType (ℝ^m) n := 
{
  powType := {a : FloatArray // a.size = n * m}
  intro := λ f => Id.run do
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
