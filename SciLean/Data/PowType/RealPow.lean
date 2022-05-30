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

structure Vec4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

structure FloatNArray (n : Nat) where
  val : FloatArray
  property : val.size = n

abbrev RealPowType (n : Nat) := 
  match n with
  | 0 => Unit
  | 1 => ℝ
  | 2 => Vec2
  | 3 => Vec3
  | 4 => Vec4
  | k+5 => FloatNArray (k+4)

def RealPowType.intro {n : Nat} (f : Idx n → ℝ) : RealPowType n := 
  match n with
  | 0 => ()
  | 1 => f !0
  | 2 => 
    ⟨f !0, f !1⟩
  | 3 => 
    ⟨f !0, f !1, f !2⟩
  | 4 => 
    ⟨f !0, f !1, f !2, f !3⟩
  | m+5 => Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in Idx.all do
      x := x.push (f i).1
    ⟨x,sorry⟩

def RealPowType.get {n : Nat} (x : RealPowType n) (i : USize) (h : i.1.1 < n) : ℝ := 
  match n with
  | 0 => 0
  | 1 => x
  | 2 => 
    match i with
    | ⟨0, _⟩ => x.x
    | ⟨1, _⟩ => x.y
  | 3 => 
    match i with
    | ⟨0, _⟩ => x.x
    | ⟨1, _⟩ => x.y
    | ⟨2, _⟩ => x.z
  | 4 => 
    match i with
    | ⟨0, _⟩ => x.x
    | ⟨1, _⟩ => x.y
    | ⟨2, _⟩ => x.z
    | ⟨3, _⟩ => x.w
  | m+5 => 
    let x : FloatNArray _ := x  -- force Lean to realize the type of x
    ⟨x.val.uget i sorry⟩

def RealPowType.set {n : Nat} (x : RealPowType n) (i : USize) (xi : ℝ) (h : i.1.1 < n) : RealPowType n := 
  match n with
  | 0 => 0
  | 1 => xi
  | 2 =>
    match i with
    | ⟨0, _⟩ => {x with x := xi}
    | ⟨1, _⟩ => {x with y := xi}
  | 3 => 
    match i with
    | ⟨0, _⟩ => {x with x := xi}
    | ⟨1, _⟩ => {x with y := xi}
    | ⟨2, _⟩ => {x with z := xi}
  | 4 => 
    match i with
    | ⟨0, _⟩ => {x with x := xi}
    | ⟨1, _⟩ => {x with y := xi}
    | ⟨2, _⟩ => {x with z := xi}
    | ⟨3, _⟩ => {x with w := xi}
  | m+5 => 
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


@[reducible] 
instance : Vec Vec2 := (by infer_instance : Vec (ℝ^(2:ℕ)))
@[reducible] 
instance : Vec Vec3 := (by infer_instance : Vec (ℝ^(3:ℕ)))

@[reducible] 
instance : Hilbert Vec2 := (by infer_instance : Hilbert (ℝ^(2:ℕ)))
@[reducible] 
instance : Hilbert Vec3 := (by infer_instance : Hilbert (ℝ^(3:ℕ)))

function_properties Vec2.mk (x y : ℝ) : Vec2
argument x
  isSmooth := sorry,
  diff_simp := ⟨dx,0⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; sorry,
  adjDiff_simp := dx'.x by sorry
argument y
  isSmooth := sorry,
  diff_simp := ⟨0,dy⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; sorry,
  adjDiff_simp := dy'.y by sorry

function_properties Vec2.x (x : ℝ^(2:ℕ)) : ℝ
argument x
  isLin := sorry, isSmooth, diff_simp,
  hasAdjoint := sorry,
  adj_simp := ⟨x',0⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
  adjDiff_simp := ⟨dx', 0⟩ by simp[adjDiff]

function_properties Vec2.y (x : ℝ^(2:ℕ)) : ℝ
argument x
  isLin := sorry, isSmooth, diff_simp,
  hasAdjoint := sorry,
  adj_simp := ⟨0,x'⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
  adjDiff_simp := ⟨0, dx'⟩ by simp[adjDiff]


function_properties Vec3.mk (x y z : ℝ) : Vec3
argument x
  isSmooth := sorry,
  diff_simp := ⟨dx,0,0⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; sorry,
  adjDiff_simp := dx'.x by sorry
argument y
  isSmooth := sorry,
  diff_simp := ⟨0,dy,0⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; sorry,
  adjDiff_simp := dy'.y by sorry
argument z
  isSmooth := sorry,
  diff_simp := ⟨0,0,dz⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; sorry,
  adjDiff_simp := dz'.z by sorry

function_properties Vec3.x (x : ℝ^(3:ℕ)) : ℝ
argument x
  isLin := sorry, isSmooth, diff_simp,
  hasAdjoint := sorry,
  adj_simp := ⟨x',0,0⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
  adjDiff_simp := ⟨dx', 0, 0⟩ by simp[adjDiff]

function_properties Vec3.y (x : ℝ^(3:ℕ)) : ℝ
argument x
  isLin := sorry, isSmooth, diff_simp,
  hasAdjoint := sorry,
  adj_simp := ⟨0,x',0⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
  adjDiff_simp := ⟨0, dx', 0⟩ by simp[adjDiff]

function_properties Vec3.z (x : ℝ^(3:ℕ)) : ℝ
argument x
  isLin := sorry, isSmooth, diff_simp,
  hasAdjoint := sorry,
  adj_simp := ⟨0,0,x'⟩ by sorry,
  hasAdjDiff := by constructor; infer_instance; simp; infer_instance,
  adjDiff_simp := ⟨0,0,dx'⟩ by simp[adjDiff]
