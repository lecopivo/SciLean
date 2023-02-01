import Lean
import SciLean.Core

namespace SciLean

-- abbrev ℝ := Float
-- instance : DecidableEq ℝ := λ x y => if x==y then .isTrue sorry else .isFalse sorry

-- structure PhysicalScale where
-- Change to rational numbers
-- Maybe change scale to positive rationals
structure PhysicalUnit where
  -- meter
  mLog10Scale  : Int := 0
  mPower      : Int   := 0
  -- second 
  sLog10Scale  : Int := 0
  sPower      : Int   := 0
  -- kilogram
  kgLog10Scale : Int := 0
  kgPower     : Int   := 0
deriving DecidableEq

def PhysicalUnit.scale (unit : PhysicalUnit) : Float := 
    2^(Float.ofInt (unit.mLog10Scale + unit.sLog10Scale + unit.kgLog10Scale))

instance : Mul PhysicalUnit := ⟨λ x y => 
  { mLog10Scale  := x.mLog10Scale + y.mLog10Scale,
    mPower      := x.mPower + y.mPower,
    sLog10Scale  := x.sLog10Scale + y.sLog10Scale,
    sPower      := x.sPower + y.sPower,
    kgLog10Scale := x.kgLog10Scale + y.kgLog10Scale,
    kgPower     := x.kgPower + y.kgPower }⟩

instance : Div PhysicalUnit := ⟨λ x y => 
  { mLog10Scale  := x.mLog10Scale - y.mLog10Scale,
    mPower      := x.mPower - y.mPower,
    sLog10Scale  := x.sLog10Scale - y.sLog10Scale,
    sPower      := x.sPower - y.sPower,
    kgLog10Scale := x.kgLog10Scale - y.kgLog10Scale,
    kgPower     := x.kgPower - y.kgPower }⟩

instance : HPow PhysicalUnit Int PhysicalUnit := ⟨λ x y => 
  { mLog10Scale  := x.mLog10Scale * y,
    mPower      := x.mPower * y,
    sLog10Scale  := x.sLog10Scale * y,
    sPower      := x.sPower * y,
    kgLog10Scale := x.kgLog10Scale * y,
    kgPower     := x.kgPower * y }⟩


instance : OfNat PhysicalUnit 1 := ⟨{}⟩


-- Maybe unit can be anything that is multiplicatie abelian group
structure PhysicalQuantity (α : Type u) (unit : PhysicalUnit) where
  val : α 

instance {α units} [Add α] : Add (PhysicalQuantity α units) := ⟨λ x y => ⟨x.val + y.val⟩⟩
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


declare_syntax_cat siunit (behavior := both)

syntax "unit" term  : siunit

def meter : PhysicalUnit := { mPower := 1}
macro "m"  : siunit => `(siunit| unit meter)

def kilometer : PhysicalUnit := { mPower := 1, mLog10Scale := 3 }
macro "km" : siunit => `(siunit| unit kilometer)

def centimeter : PhysicalUnit := { mPower := 1, mLog10Scale := -2 }
macro "cm" : siunit => `(siunit| unit centimeter)

def millimeter : PhysicalUnit := { mPower := 1, mLog10Scale := -3 }
macro "mm" : siunit => `(siunit| unit millimeter)

def mile : PhysicalUnit := { mPower := 1, mLog10Scale := Float.log10 1609.34 |>.toUInt64.toNat}
macro "mi" : siunit => `(siunit| unit mile)

def yard : PhysicalUnit := { mPower := 1, mLog10Scale := Float.log10 0.9144 |>.toUInt64.toNat}
macro "yd" : siunit => `(siunit| unit yard)

def feet : PhysicalUnit := { mPower := 1, mLog10Scale := Float.log10 0.3048 |>.toUInt64.toNat}
macro "ft" : siunit => `(siunit| unit feet)

def inch : PhysicalUnit := { mPower := 1, mLog10Scale := Float.log10 0.0254 |>.toUInt64.toNat}
macro "in" : siunit => `(siunit| unit inch)


def hectare : PhysicalUnit := { mPower := 2, mLog10Scale := 4 }
macro "ha" : siunit => `(siunit| unit hectare)

def acre : PhysicalUnit := { mPower := 2, mLog10Scale := Float.log10 4046.86 |>.toUInt64.toNat}
macro "ac" : siunit => `(siunit| unit acre)

def second : PhysicalUnit := { sPower := 1 }
macro "s" : siunit => `(siunit| unit second)

def minute : PhysicalUnit := { sPower := 1, sLog10Scale := Float.log10 60 |>.toUInt64.toNat}
macro "min" : siunit => `(siunit| unit minute)

def hour : PhysicalUnit := { sPower := 1, sLog10Scale := Float.log10 360 |>.toUInt64.toNat}
macro "h" : siunit => `(siunit| unit hour)

def day : PhysicalUnit := { sPower := 1, sLog10Scale := Float.log10 8640 |>.toUInt64.toNat}
macro "day" : siunit => `(siunit| unit day)

def kilogram : PhysicalUnit := { kgPower := 1 }
macro "kg" : siunit => `(siunit| unit kilogram)

def gram : PhysicalUnit := { kgPower := 1, kgLog10Scale := -3}
macro "g" : siunit => `(siunit| unit gram)

def milligram : PhysicalUnit := { kgPower := 1, kgLog10Scale := -6}
macro "mg" : siunit => `(siunit| unit milligram)

def stone : PhysicalUnit := { kgPower := 1, kgLog10Scale := Float.log10 6.350288000002350941 |>.toUInt64.toNat}
macro "st" : siunit => `(siunit| unit stone)

def pound : PhysicalUnit := { kgPower := 1, kgLog10Scale := Float.log10 0.4535920000001679 |>.toUInt64.toNat}
macro "Lb" : siunit => `(siunit| unit pound)

def ounce : PhysicalUnit := { kgPower := 1, kgLog10Scale := Float.log10 0.028349500000010494777 |>.toUInt64.toNat}
macro "oz" : siunit => `(siunit| unit ounce)


def hertz : PhysicalUnit := { sPower := -1 }
macro "Hz" : siunit => `(siunit| unit hertz)

def newton : PhysicalUnit := { mPower := 1, sPower := -2, kgPower := 1 }
macro "N" : siunit => `(siunit| unit newton)

def pascal : PhysicalUnit := { mPower := -1, sPower := -2, kgPower := 1 }
macro "Pa" : siunit => `(siunit| unit pascal)

def watt : PhysicalUnit := { mPower := 2, sPower := -3, kgPower := 1 }
macro "W" : siunit => `(siunit| unit watt)

def joule : PhysicalUnit := { mPower := 2, sPower := -2, kgPower := 1 }
macro "J" : siunit => `(siunit| unit joule)


syntax siunit:71 "*" siunit:70 : siunit
syntax siunit:71 "/" siunit:70 : siunit
syntax siunit noWs "²" : siunit
syntax siunit noWs "³" : siunit
syntax siunit noWs "⁻¹" : siunit
syntax siunit noWs "⁻²" : siunit
syntax siunit noWs "⁻³" : siunit

syntax "ℝ[" siunit "]" : term

macro_rules
| `(siunit| $unit * $unit') => do
  match (← Lean.expandMacros unit) with 
  | `(siunit| unit $u) => 
    match (← Lean.expandMacros unit') with
    | `(siunit| unit $u') => 
      `(siunit| unit ($u * $u'))
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported
| `(siunit| $unit / $unit') => do
  match (← Lean.expandMacros unit) with 
  | `(siunit| unit $u) => 
    match (← Lean.expandMacros unit') with
    | `(siunit| unit $u') => 
      `(siunit| unit ($u / $u'))
    | _ => Lean.Macro.throwUnsupported
  | _ => Lean.Macro.throwUnsupported
| `(siunit| $unit²) => do
  match (← Lean.expandMacros unit) with
  | `(siunit| unit $u) => `(siunit| unit $u^(2:Int))
  | _ => Lean.Macro.throwUnsupported
| `(siunit| $unit³) => do
  match (← Lean.expandMacros unit) with
  | `(siunit| unit $u) => `(siunit| unit $u^(3:Int))
  | _ => Lean.Macro.throwUnsupported
| `(siunit| $unit⁻¹) => do
  match (← Lean.expandMacros unit) with
  | `(siunit| unit $u) => `(siunit| unit $u^(-1:Int))
  | _ => Lean.Macro.throwUnsupported
| `(siunit| $unit⁻²) => do
  match (← Lean.expandMacros unit) with
  | `(siunit| unit $u) => `(siunit| unit $u^(-2:Int))
  | _ => Lean.Macro.throwUnsupported
| `(siunit| $unit⁻³) => do
  match (← Lean.expandMacros unit) with
  | `(siunit| unit $u) => `(siunit| unit $u^(-3:Int))
  | _ => Lean.Macro.throwUnsupported
| `(ℝ[ $units ]) => do
  match (← Lean.expandMacros units) with
  | `(siunit| unit $u) => `(PhysicalQuantity ℝ $u)
  | _ => Lean.Macro.throwUnsupported


open Lean Lean.Meta Lean.Elab Lean.Elab.Term in
elab_rules : term
| `(PhysicalQuantity $α $unit) => do
  let α ← elabTerm α none
  let unit ← reduce (← elabTerm unit (mkConst ``PhysicalUnit))
  mkAppM ``PhysicalQuantity #[α, unit]


example : ℝ[mm*km] = ℝ[m²] := by rfl
example : ℝ[m*s⁻¹] = ℝ[s⁻¹*m] := by rfl
example : ℝ[kg*mg] = ℝ[g²] := by rfl

example : ℝ[N]  = ℝ[kg*m*s⁻²] := by rfl
example : ℝ[J]  = ℝ[N*m]   := by rfl
example : ℝ[W]  = ℝ[J*s⁻¹] := by rfl
example : ℝ[Pa] = ℝ[N*m⁻²] := by rfl

example : ℝ[N*m²*kg⁻²] = ℝ[m³*kg⁻¹*s⁻²] := by rfl
example : ℝ[J*Hz⁻¹] = ℝ[J*s] := by rfl

namespace PhysicalConstants 
  --- Source: https://en.wikipedia.org/wiki/Physical_constant#Table_of_physical_constants

  def gravitationalConstant : ℝ[N*m²*kg⁻²] := ⟨6.674 * 10.0^(-11.0)⟩
  abbrev G := gravitationalConstant

  def speedOfLight : ℝ[m*s⁻¹] := ⟨299792458.0⟩
  abbrev c := speedOfLight

  def planckConstant : ℝ[J*Hz⁻¹] := ⟨6.62607015 * 10.0^(-34.0)⟩
  abbrev h := planckConstant
  abbrev ℎ := planckConstant

  def reducedPlanckConstant : ℝ[J*s] := h / Math.pi
  abbrev ℏ := reducedPlanckConstant

  def electronMass : ℝ[kg] := ⟨9.1093837015 * 10.0^(-31.0)⟩
  abbrev mₑ : ℝ[kg] := electronMass

end PhysicalConstants
