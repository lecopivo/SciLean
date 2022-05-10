import SciLean.Data.PowType.Basic
import SciLean.Data.PowType.Algebra

namespace SciLean

structure Vec2 where
  x : ℝ
  y : ℝ

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ

structure FloatNArray (n : Nat) where
  val : FloatArray
  property : val.size = n

abbrev RealPowType (n : Nat) := 
  match n with
  | 0 => Unit
  | 1 => ℝ
  | 2 => Vec2
  | 3 => Vec3
  | k+4 => FloatNArray (k+4)

def RealPowType.intro {n : Nat} (f : Idx n → ℝ) : RealPowType n := 
  match n with
  | 0 => ()
  | 1 => f !0
  | 2 => 
    ⟨f !0, f !1⟩
  | 3 => 
    ⟨f !0, f !1, f !2⟩
  | m+4 => Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in Idx.all do
      x := x.push (f i).1
    ⟨x,sorry⟩

def RealPowType.get {n : Nat} (x : RealPowType n) (i : USize) (h : i.1 < n) : ℝ := 
  match n with
  | 0 => 0
  | 1 => x
  | 2 => if i = 0 then x.x else x.y
  | 3 => if i = 0 then x.x else if i = 1 then x.y else x.z
  | m+4 => 
    let x : FloatNArray _ := x  -- force Lean to realize the type of x
    ⟨x.val.uget i sorry⟩

def RealPowType.set {n : Nat} (x : RealPowType n) (i : USize) (xi : ℝ) (h : i.1 < n) : RealPowType n := 
  match n with
  | 0 => 0
  | 1 => xi
  | 2 => if i = 0 then {x with x := xi} else {x with y := xi}
  | 3 => 
    if i = 0 then
      {x with x := xi} 
    else if i = 1 then 
      {x with y := xi} 
    else 
      {x with z := xi}
  | m+4 => 
    let x : FloatNArray _ := x
    ⟨x.1.uset i xi.1 sorry, sorry⟩

instance : PowType ℝ := 
{
  powType := RealPowType
  intro := RealPowType.intro
  get := λ x i => RealPowType.get x i.1 sorry
  set := λ x i xi => RealPowType.set x i.1 xi sorry
  ext := sorry
}

instance (m : Nat) : PowType (ℝ^m) := 
{
  powType := λ n => {a : FloatArray // a.size = n * m}
  intro := λ {n} f => Id.run do
    let mut x := FloatArray.mkEmpty (n*m)
    for i in Idx.all do
      let xi := (f i)
      for j in Idx.all do
        x := x.push (xi[j]).val
    !x
  get := λ x i => 
    PowType.intro λ j => ⟨x.1.uget (i.1*m + j.1) sorry⟩
  set := λ x i xi => Id.run do
    let mut x := x.1
    let offset := i.1*m
    for j in Idx.all do
      x := x.uset (j.1 + offset) (xi[j]).val sorry
    !x
  ext := sorry
}
