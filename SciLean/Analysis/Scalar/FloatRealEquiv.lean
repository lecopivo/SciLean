import Mathlib.Data.Real.Basic
import SciLean.Tactic.DataSynth.Elab
import SciLean.Tactic.DataSynth.Attr

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


@[data_synth out g in f]
structure RealToFloatFun {R₁ R₂ : Type} {F₁ F₂ : outParam Type}
  [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂]
  (f : R₁ → R₂) (g : F₁ → F₂) : Prop where


namespace RealToFloatFun

variable {R R₁ R₂ R₃ F F₁ F₂ F₃ : Type}
  [RealToFloatType R F] [RealToFloatType R₁ F₁] [RealToFloatType R₂ F₂] [RealToFloatType R₃ F₃]


opaque realToFloatVal [Inhabited F] [RealToFloatType R F] : R → F

@[data_synth]
theorem id_rule : RealToFloatFun (fun x : R => x) (fun x : F => x) := ⟨⟩
theorem const_rule [Inhabited F₂] (y : R₂) : RealToFloatFun (fun x : R₁ => y) (fun x : F₁ => realToFloatVal y) := ⟨⟩
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
theorem HAdd.hAdd.arg_a0a1.RealToFloatFun_rule'
  (f g : R → ℝ) (f' g') (hf : RealToFloatFun f f') (hg : RealToFloatFun g g') :
  RealToFloatFun (fun x : R => f x + g x) (fun x => f' x + g' x) := ⟨⟩


@[data_synth]
theorem Prod.fst.arg_self.RealToFloatFun_rule'
  (f : R → R₁×R₂) (f') (hf : RealToFloatFun f f') :
  RealToFloatFun (fun x : R => (f x).1) (fun x => (f' x).1) := ⟨⟩

@[data_synth]
theorem Prod.snd.arg_self.RealToFloatFun_rule'
  (f : R → R₁×R₂) (f') (hf : RealToFloatFun f f') :
  RealToFloatFun (fun x : R => (f x).2) (fun x => (f' x).2) := ⟨⟩

theorem HAdd.hAdd.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 + x.2) (fun x => x.1 + x.2) := ⟨⟩
theorem HSub.hSub.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 - x.2) (fun x => x.1 - x.2) := ⟨⟩
theorem HMul.hMul.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 * x.2) (fun x => x.1 * x.2) := ⟨⟩
theorem HDiv.hDiv.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 / x.2) (fun x => x.1 / x.2) := ⟨⟩

theorem Neg.neg.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ => -x) (fun x => -x) := ⟨⟩
theorem Inv.inv.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ => x⁻¹) (fun x => 1/x) := ⟨⟩

theorem Eq.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 = x.2) (fun x => (x.1 - x.2).abs ≤ Float.eps) := ⟨⟩
theorem LT.lt.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 < x.2) (fun x => x.1 < x.2) := ⟨⟩
theorem LE.le.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 ≤ x.2) (fun x => x.1 ≤ x.2) := ⟨⟩
theorem GT.gt.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 > x.2) (fun x => x.1 > x.2) := ⟨⟩
theorem GE.ge.arg_a0a1.RealToFloatFun_rule : RealToFloatFun (fun x : ℝ×ℝ => x.1 ≥ x.2) (fun x => x.1 ≥ x.2) := ⟨⟩


#check (RealToFloatFun (fun x : ℝ => let y := x + x; let z := x + y; y + z + x + x + x) _)
  rewrite_by
    data_synth
