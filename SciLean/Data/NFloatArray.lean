import SciLean.Data.FunType

namespace SciLean

def NFloatArray (n : Nat) := {a : FloatArray // n = a.size}

namespace NFloatArray 

  def get {n} (a : NFloatArray n) (i : Fin n) := a.1.get (a.2 ▸ i)
  def getOp {n} (self : NFloatArray n) (idx : Fin n) := self.get idx

  def set {n} (a : NFloatArray n) (i : Fin n) (ai : Float) : NFloatArray n :=
    ⟨a.1.set (a.2 ▸ i) ai, sorry⟩

  def intro {n} (f : Fin n → Float) : NFloatArray n := sorry

  instance : GetElem (NFloatArray n) (Fin n) Float (λ _ _ => True) where
    getElem a i _ := a.get i
  instance : FunType (NFloatArray n) (Fin n) Float where
    ext := sorry

  instance [Enumtype ι] : GetElem (NFloatArray (numOf ι)) ι Float (λ _ _ => True) where
    getElem a i _ := a.get (toFin i)
  instance [Enumtype ι] : FunType (NFloatArray (numOf ι)) ι Float where
    ext := sorry

  open FunType

  instance : SetElem (NFloatArray n) (Fin n) Float where
    setElem a i ai := a.set i ai
  instance : HasSet (NFloatArray n) where
    toFun_set_eq  := sorry
    toFun_set_neq := sorry

  instance [Enumtype ι] : SetElem (NFloatArray (numOf ι)) ι Float where
    setElem a i ai := a.set (toFin i) ai
  instance [Enumtype ι] : HasSet (NFloatArray (numOf ι)) where
    toFun_set_eq  := sorry
    toFun_set_neq := sorry

  instance : HasIntro (NFloatArray n) where
    intro f := intro f

    toFun_intro := sorry

  -- TODO: This can can a faster implementation using `Iterable.next`
  instance [Enumtype ι] : HasIntro (NFloatArray (numOf ι)) where
    intro f := intro (λ i => f (fromFin i))

    toFun_intro := sorry


end NFloatArray 
