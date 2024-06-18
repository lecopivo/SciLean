import Lean
import Batteries
import Qq
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SciLean

structure PhysicalUnit where
  scale : ℚ := 1
  mPower : ℤ := 0
  sPower : ℤ := 0
  kgPower : ℤ := 0
deriving DecidableEq

instance : Mul PhysicalUnit := ⟨λ x y =>
  { scale := x.scale * y.scale
    mPower  := x.mPower + y.mPower,
    sPower  := x.sPower + y.sPower,
    kgPower := x.kgPower + y.kgPower }⟩

instance : Div PhysicalUnit := ⟨λ x y =>
  { scale  := x.scale / y.scale,
    mPower  := x.mPower - y.mPower,
    sPower  := x.sPower - y.sPower,
    kgPower := x.kgPower - y.kgPower }⟩

instance : HPow PhysicalUnit Int PhysicalUnit := ⟨λ x y =>
  { scale  := x.scale ^ y,
    mPower  := x.mPower * y,
    sPower  := x.sPower * y,
    kgPower := x.kgPower * y }⟩

instance : HPow PhysicalUnit Nat PhysicalUnit := ⟨λ x y =>
  { scale  := x.scale ^ y,
    mPower  := x.mPower * y,
    sPower  := x.sPower * y,
    kgPower := x.kgPower * y }⟩


@[simp]
theorem PhysicalUnit.div_to_mk (u v : PhysicalUnit)
  : u / v
    =
    PhysicalUnit.mk (u.scale/v.scale) (u.mPower - v.mPower) (u.sPower - v.sPower) (u.kgPower - v.kgPower) := by rfl

@[simp]
theorem PhysicalUnit.mul_to_mk (u v : PhysicalUnit)
  : u * v
    =
    PhysicalUnit.mk (u.scale*v.scale) (u.mPower + v.mPower) (u.sPower + v.sPower) (u.kgPower + v.kgPower) := by rfl

@[simp]
theorem PhysicalUnit.pow_mk (u : PhysicalUnit) (x : Int)
  : u ^ x
    =
    PhysicalUnit.mk (u.scale^x) (u.mPower*x) (u.sPower*x) (u.kgPower*x) := by rfl

@[simp]
theorem PhysicalUnit.pow_mk' (u : PhysicalUnit) (x : Nat)
  : u ^ x
    =
    PhysicalUnit.mk (u.scale^x) (u.mPower*x) (u.sPower*x) (u.kgPower*x) := by rfl

instance : One PhysicalUnit := ⟨{}⟩

@[simp]
theorem PhysicalUnit.one_scale
  : (1 : PhysicalUnit).scale = 1 := by rfl

@[simp]
theorem PhysicalUnit.one_mpower
  : (1 : PhysicalUnit).mPower = 0 := by rfl

@[simp]
theorem PhysicalUnit.one_spower
  : (1 : PhysicalUnit).sPower = 0 := by rfl

@[simp]
theorem hPhysicalUnit.one_kgpower
  : (1 : PhysicalUnit).kgPower = 0 := by rfl

structure PhysicalQuantity (α : Type u) (unit : PhysicalUnit := {}) where
  val : α

instance {α units} [Add α] : Add (PhysicalQuantity α units) := ⟨λ x y => ⟨x.val + y.val⟩⟩
instance {α units} [Sub α] : Sub (PhysicalQuantity α units) := ⟨λ x y => ⟨x.val - y.val⟩⟩
instance {α units} [OfNat α n] : OfNat (PhysicalQuantity α units) n := ⟨⟨OfNat.ofNat n⟩⟩

instance {α β γ units units'} [HMul α β γ]
  : HMul (PhysicalQuantity α units) (PhysicalQuantity β units') (PhysicalQuantity γ (units*units')) :=
  ⟨λ x y => ⟨x.val * y.val⟩⟩
instance {α β γ units} [HMul α β γ]
  : HMul (PhysicalQuantity α units) β (PhysicalQuantity γ (units)) :=
  ⟨λ x y => ⟨x.val * y⟩⟩
instance {α β γ units'} [HMul α β γ]
  : HMul α (PhysicalQuantity β units') (PhysicalQuantity γ (units')) :=
  ⟨λ x y => ⟨x * y.val⟩⟩

instance {α β γ units units'} [HDiv α β γ]
  : HDiv (PhysicalQuantity α units) (PhysicalQuantity β units') (PhysicalQuantity γ (units/units')) :=
  ⟨λ x y => ⟨x.val / y.val⟩⟩
instance {α β γ units} [HDiv α β γ]
  : HDiv (PhysicalQuantity α units) β (PhysicalQuantity γ (units)) :=
  ⟨λ x y => ⟨x.val / y⟩⟩
instance {α β γ units'} [HDiv α β γ]
  : HDiv α (PhysicalQuantity β units') (PhysicalQuantity γ (1/units')) :=
  ⟨λ x y => ⟨x / y.val⟩⟩

abbrev meter : PhysicalUnit := { mPower := 1}
abbrev kilometer : PhysicalUnit := { mPower := 1, scale := 1000 }
abbrev centimeter : PhysicalUnit := { mPower := 1, scale := (1:ℚ)/(100:ℚ) }
abbrev millimeter : PhysicalUnit := { mPower := 1, scale := (1:ℚ)/(1000:ℚ) }
abbrev mile : PhysicalUnit := { mPower := 1, scale := (160934:ℚ)/(100:ℚ) }
abbrev second : PhysicalUnit := { sPower := 1 }
abbrev minute : PhysicalUnit := { sPower := 1, scale := 60}
abbrev hour : PhysicalUnit := { sPower := 1, scale := 360}
abbrev day : PhysicalUnit := { sPower := 1, scale := 8640}
abbrev kilogram : PhysicalUnit := { kgPower := 1 }
abbrev gram : PhysicalUnit := { kgPower := 1, scale := (1:ℚ)/(1000:ℚ)}
abbrev milligram : PhysicalUnit := { kgPower := 1, scale := (1:ℚ)/(1000000:ℚ)}
abbrev hertz : PhysicalUnit := { sPower := -1 }
abbrev newton : PhysicalUnit := { mPower := 1, sPower := -2, kgPower := 1 }
abbrev pascal : PhysicalUnit := { mPower := -1, sPower := -2, kgPower := 1 }
abbrev watt : PhysicalUnit := { mPower := 2, sPower := -3, kgPower := 1 }
abbrev joule : PhysicalUnit := { mPower := 2, sPower := -2, kgPower := 1 }

open Lean Meta Qq in
#eval show MetaM Unit from do
  let a := q((1:ℚ) + (1:ℚ))
  let b := q((2:ℚ))
  IO.println s!"Is {← ppExpr a} defeq to {b}: {← isDefEq a b}"
  let a := q((3:ℚ) * (2:ℚ) / (3:ℚ))
  let b := q((2:ℚ))
  IO.println s!"Is {← ppExpr a} defeq to {← ppExpr b}: {← isDefEq a b}"

syntax term noWs "⟦" term "⟧ ": term

macro_rules
| `(term| $X:term⟦ $unit:term ⟧) => `(PhysicalQuantity $X $unit)

@[app_unexpander PhysicalQuantity] def unexpandPhysicalQuantity : Lean.PrettyPrinter.Unexpander

  | `($(_) $α:term { scale := $a, mPower := $b, sPower := $c, kgPower := $d}) => do
    let zero ← `(0)
    let one ← `(1)
    let meter := Lean.mkIdent ``meter
    let second := Lean.mkIdent ``second
    let kilogram := Lean.mkIdent ``kilogram
    let unit : Array (Lean.TSyntax `term) ← #[(b,meter),(c,second),(d,kilogram)].filterMapM
      (fun (x,y) => do
        if x == zero then
          pure none
        else if x == one then
          pure (.some y)
        else
          pure $ .some (← `(term| $y ^ $x)))

    let unit ← unit[1:].foldlM (init:=unit[0]!) (fun a b => `(term| $a * $b))

    if a == one then
      `(term| $α:term⟦$unit⟧)
    else
      `(term| $a * $α:term⟦$unit⟧)

  | `($(_) $α:term $u) => `($α⟦$u⟧)

  | _  => throw ()

example : Float⟦millimeter*kilometer⟧ = Float⟦meter^2⟧ := by rfl
example : ℚ⟦meter*second^(-1)⟧ = ℚ⟦second^(-1)*meter⟧ := by rfl
example : ℕ⟦kilogram*milligram⟧ = ℕ⟦gram^2⟧ := by rfl
example : Float⟦newton⟧  = Float⟦kilogram*meter*second^(-2)⟧ := by rfl

open Lean Elab Term Meta Qq in
elab (priority:=high) x:term:71 " * " y:term:70 : term => do
  let x ← elabTerm x none
  let y ← elabTerm y none
  let X ← inferType x
  let Y ← inferType y
  let z ← mkAppOptM ``HMul.hMul #[X,Y,none,none,x,y]
  let Z ← inferType z
  let r ← Mathlib.Meta.NormNum.deriveSimp
    { simpTheorems := #[← getSimpTheorems],
      congrTheorems := ← getSimpCongrTheorems} true Z
  let Z' := r.expr
  dbg_trace s!"Is {← ppExpr Z} defeq to {← ppExpr Z'}: {← isDefEq Z Z'}"
  if ← isDefEq Z Z' then
    let mul ← synthInstance (← mkAppOptM ``HMul #[X,Y,Z])
    mkAppOptM ``HMul.hMul #[X,Y,Z',mul,x,y]
  else
    mkAppOptM ``cast #[none,none,r.proof?,z]


open Lean Elab Term Meta Qq in
elab (priority := high) x:term:66 " + " y:term:65 : term => do
  let x ← elabTerm x none
  let y ← elabTerm y none

  try
    mkAppOptM ``HAdd.hAdd #[none,none,none,none,x,y]
  catch _ =>

    let X ← inferType x
    let Y ← inferType y

    let ctx : Simp.Context :=
      { simpTheorems := #[← getSimpTheorems],
        congrTheorems := ← getSimpCongrTheorems}

    let rX ← Mathlib.Meta.NormNum.deriveSimp ctx true X
    let rY ← Mathlib.Meta.NormNum.deriveSimp ctx true Y

    let x' ←
      match rX.proof? with
      | some proof => mkAppOptM ``cast #[X,rX.expr,proof,x]
      | none => pure x
    let y' ←
      match rY.proof? with
      | some proof => mkAppOptM ``cast #[Y,rY.expr,proof,y]
      | none => pure y

    mkAppOptM ``HAdd.hAdd #[none,none,none,none,x',y']


variable
  (v₁ : Float⟦meter*second^(-1:Int)⟧) (v₂ : Float⟦kilometer*hour^(-1:Int)⟧) (v₃ : Float⟦meter*hour^(-1:Int)⟧)
  (t₁ : Float⟦second⟧) (t₂ : Float⟦hour⟧)
  (a  : Float⟦meter*second^(-2:Int)⟧)
  (p : Float⟦pascal⟧) (V : Float⟦meter^3⟧) (R : Float⟦joule⟧) (F : Float⟦newton⟧)


set_option pp.proofs.withType false


#check v₁ * t₁   -- Float⟦m⟧
#check v₂ * t₂   -- Float⟦1000*m⟧
#check v₂ * t₁   -- Float⟦25/9*m*s⁻¹⟧    note: 1000/360 = 25/9
#check (v₁ * t₁) + (a * t₁ * t₁) + (t₁ * a * t₁) + (t₁ * t₁ * a)  -- Float⟦m⟧

#check_failure (v₁ * t₁) + (v₂ * t₂) -- fails to add Float⟦m⟧ and Float⟦1000*m⟧

instance : One PhysicalUnit := ⟨{}⟩

def uderiv {X Y : Type} {u v w : PhysicalUnit} (f : X⟦u⟧ → Y⟦v⟧) (x : X⟦u⟧) (dx : X⟦w⟧) : Y⟦(v*w)/u⟧ := sorry

variable
  (u : ℝ⟦second⟧ → ℝ⟦meter⟧ → ℝ⟦meter*second^(-1:Int)⟧)
  (p : ℝ⟦second⟧ → ℝ⟦meter⟧ → ℝ⟦pascal⟧)
  (density : ℝ⟦second⟧ → ℝ⟦meter⟧ → ℝ⟦kilogram*meter^(-3:Int)⟧)
  (ν : ℝ⟦(meter^(2:Int)) * second^(-1:Int)⟧)

#check fun t x => (uderiv (u · x) t (1:ℝ⟦1⟧))                              -- ∂u/∂t
                + (uderiv (u t ·) x (u t x))                                -- (u⬝∇)u
                + (((1:ℝ⟦1⟧) / density t x) * uderiv (p t ·) x (1:ℝ⟦1⟧))   -- 1/ρ ∇p
                + ν * uderiv ((uderiv (u t ·)) · (1:ℝ⟦1⟧)) x (1:ℝ⟦1⟧)      -- ν Δu


def adjoint {X Y : Type} {u v : PhysicalUnit} (f : X⟦u⟧ → Y⟦v⟧) : Y⟦v⟧ → X⟦u⟧ := sorry

def uderiv' {X Y : Type} {u v w : PhysicalUnit} [Group PhysicalUnit] (f : X⟦u⟧ → Y⟦v⟧) (x : X⟦u⟧) (dy : Y⟦w⟧) : X⟦(u*w)/v⟧ :=
  let df := fun dx : X⟦(u*w)/v⟧ => uderiv f x dx
  let df' := adjoint df
  df' (cast (by congr; have h : w.scale = (v.scale * ((u.scale * w.scale) / v.scale)) / u.scale := sorry; cases w; simp at h; simp; exact h) dy)



variable
  (u : ℝ⟦time,s⟧ → ℝ⟦length,s'⟧ → ℝ⟦length*time^(-1),s''⟧)
  (p : ℝ⟦second⟧ → ℝ⟦meter⟧ → ℝ⟦pascal⟧)
  (density : ℝ⟦second⟧ → ℝ⟦meter⟧ → ℝ⟦kilogram*meter^(-3:Int)⟧)
  (ν : ℝ⟦(meter^(2:Int)) * second^(-1:Int)⟧)

def ucast {X : Type _} {u : PhysicalUnit} (v : PhysicalUnit)
