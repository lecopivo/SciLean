import Mathlib.Data.Real.Basic
-- import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
-- import Mathlib.AlgebraicGeometry.EllipticCurve.Projective

import SciLean.Analysis.Scalar.FloatAsReal
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.DataSynth.Attr

set_option linter.unusedVariables false

namespace SciLean

/-- Class indicating that type `RealType` containing real values corresponds to type `FloatType`
containing equivalent floats.

It is difficult to say what does this supposed to satisfy. Therefore it is empty class that is
used only as a tag for metaprogramming purposed. -/
class RealFloatEquiv (RealType FloatType : Type*) : Prop where

class RealToFloatType (RealType : Type*) (FloatType : outParam Type*)

/-- Type `T` doe not contain any real numbers in it and should be preserved by Real -> Float
conversion -/
class NotRealType (T : Type*) where
instance [NotRealType T] : RealToFloatType T T := ⟨⟩

instance : RealToFloatType ℝ Float := ⟨⟩

-- basic types are unchanged
instance : NotRealType (Sort u) := ⟨⟩
instance : NotRealType Unit := ⟨⟩
instance : NotRealType Empty := ⟨⟩
instance : NotRealType Bool := ⟨⟩
instance : NotRealType ℕ := ⟨⟩
instance : NotRealType ℤ := ⟨⟩
instance : NotRealType ℚ := ⟨⟩

-- basic type constructors
-- variable {R R₁ R₂ F F₁ F₂ : Type*}
--   [RealToFloatType R F] [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂]

instance [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂] : RealToFloatType (R₁ → R₂) (F₁ → F₂) := ⟨⟩
instance [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂] : RealToFloatType (R₁ × R₂) (F₁ × F₂) := ⟨⟩

instance [RealToFloatType R F] : RealToFloatType (Option R) (Option F) := ⟨⟩
instance [RealToFloatType R F] : RealToFloatType (Array R) (Array F) := ⟨⟩
instance [RealToFloatType R F] : RealToFloatType (List R) (List F) := ⟨⟩


@[data_synth out f]
structure RealToFloatVal {R : Type} {F : outParam Type}
  [RealToFloatType R F]
  (r : R) (f : F) : Prop where

@[data_synth out g in f]
structure RealToFloatFun {R₁ R₂ : Type} {F₁ F₂ : outParam Type}
  [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂]
  (f : R₁ → R₂) (g : F₁ → F₂) : Prop where


namespace RealToFloatFun

variable {R R₁ R₂ R₃ F F₁ F₂ F₃ : Type}
  [RealToFloatType R F] [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂] [RealToFloatType R₃ F₃]


@[data_synth]
theorem id_rule : RealToFloatFun (fun x : R => x) (fun x : F => x) := ⟨⟩

theorem const_rule [Inhabited F₂] (hy : RealToFloatVal (y : R₂) (y' : F₂)) :
     RealToFloatFun (fun x : R₁ => y) (fun x : F₁ => y') := ⟨⟩

theorem comp_rule (f : R₂ → R₃) (g : R₁ → R₂) (f' g')
    (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
    RealToFloatFun (fun x => f (g x)) (fun x => f' (g' x)) := ⟨⟩

theorem let_rule (g : R₁ → R₂) (f : R₂ → R₁ → R₃) (f' g')
    (hg : RealToFloatFun g g') (hf : RealToFloatFun (fun x : R₂×R₁ => f x.1 x.2) f')  :
    RealToFloatFun (fun x => let y := g x; f y x) (fun x => let y := g' x; f' (y,x)) := ⟨⟩

end RealToFloatFun


-- maybe consider using these
def _root_.Float.eps : Float := 1e-15
def _root_.Float.safeDiv (x y : Float) := if y.abs ≤ Float.eps then 0 else x / y
def _root_.Float.safeInv (x : Float) := if x.abs ≤ Float.eps then 0 else 1 / x

variable {R R₁ R₂ R₃ F F₁ F₂ F₃ : Type}
  [RealToFloatType R F] [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂] [RealToFloatType R₃ F₃]


@[data_synth]
theorem Prod.fst.arg_self.RealToFloatFun_rule'
  (f : R → R₁×R₂) (f') (hf : RealToFloatFun f f') :
  RealToFloatFun (fun x : R => (f x).1) (fun x => (f' x).1) := ⟨⟩

@[data_synth]
theorem Prod.snd.arg_self.RealToFloatFun_rule'
  (f : R → R₁×R₂) (f') (hf : RealToFloatFun f f') :
  RealToFloatFun (fun x : R => (f x).2) (fun x => (f' x).2) := ⟨⟩

@[data_synth]
theorem realToFloatVal_notRealType [NotRealType S] (s : S) : RealToFloatVal s s := ⟨⟩


----------------------------------------------------------------------------------------------------
-- Besic operations on Reals -----------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


@[data_synth]
theorem HAdd.hAdd.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x + g x) (fun x => f' x + g' x) := ⟨⟩

@[data_synth]
theorem HMul.hMul.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x * g x) (fun x => f' x * g' x) := ⟨⟩

@[data_synth]
theorem HDiv.hDiv.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x / g x) (fun x => f' x / g' x) := ⟨⟩

@[data_synth]
theorem HPow.hPow.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x ^ g x) (fun x => f' x ^ g' x) := ⟨⟩

@[data_synth]
theorem Neg.neg.arg_a0a1.RealToFloatFun_rule'
  (f : R → ℝ) (f') (hf : RealToFloatFun f f') :
  RealToFloatFun (fun x : R => - f x) (fun x => - f' x) := ⟨⟩

@[data_synth]
theorem Inv.inv.arg_a0a1.RealToFloatFun_rule'
  (f : R → ℝ) (f') (hf : RealToFloatFun f f') :
  RealToFloatFun (fun x : R => (f x)⁻¹) (fun x => 1 / f' x) := ⟨⟩

@[data_synth]
theorem Eq.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x = g x) (fun x => (f' x - g' x).abs ≤ Float.eps) := ⟨⟩

@[data_synth]
theorem LT.lt.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x < g x) (fun x => f' x < g' x) := ⟨⟩

@[data_synth]
theorem LE.le.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x ≤ g x) (fun x => f' x ≤ g' x) := ⟨⟩

@[data_synth]
theorem GT.gt.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x > g x) (fun x => f' x > g' x) := ⟨⟩

@[data_synth]
theorem GE.ge.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x ≥ g x) (fun x => f' x ≥ g' x) := ⟨⟩

@[data_synth]
theorem One.one.RealToFloatVal_ruel : RealToFloatVal (1:ℝ) (1:Float) := ⟨⟩

@[data_synth]
theorem Zero.zero.RealToFloatVal_ruel : RealToFloatVal (0:ℝ) (0:Float) := ⟨⟩

@[data_synth]
theorem nat_coe_RealtoFloatVal_rule (n : ℕ) : RealToFloatVal (n : ℝ) (n.toFloat) := ⟨⟩

@[data_synth]
theorem OfNat.ofNat.RealtoFloatVal_rule
    {n : ℕ} [NatCast ℝ] [Nat.AtLeastTwo n] : RealToFloatVal (OfNat.ofNat n : ℝ) (OfNat.ofNat n : Float) := ⟨⟩

@[data_synth]
theorem ofScientific.RealToFloatVal_rule :
    RealToFloatVal (OfScientific.ofScientific n b m :ℝ) (OfScientific.ofScientific n b m :Float) := ⟨⟩
