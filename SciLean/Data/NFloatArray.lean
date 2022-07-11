import SciLean.Data.FunType

namespace SciLean

def NFloatArray (n : Nat) := {a : FloatArray // n = a.size}

namespace NFloatArray 

  def get {n} (a : NFloatArray n) (i : Fin n) := a.1.get (a.2 ▸ i)
  def getOp {n} (self : NFloatArray n) (idx : Fin n) := self.get idx

  def set {n} (a : NFloatArray n) (i : Fin n) (ai : Float) : NFloatArray n :=
    ⟨a.1.set (a.2 ▸ i) ai, sorry⟩

  def intro {n} (f : Fin n → Float) : NFloatArray n := sorry

  instance : FunType (NFloatArray n) (Fin n) Float where
    toFun a i := a.get i

    ext := sorry

  instance [Enumtype ι] : FunType (NFloatArray (numOf ι)) ι Float where
    toFun a i := a.get (toFin i)

    ext := sorry

  open FunType

  instance : HasSet (NFloatArray n) where
    set a i ai := a.set i ai

    toFun_set_eq  := sorry
    toFun_set_neq := sorry

  instance [Enumtype ι] : HasSet (NFloatArray (numOf ι)) where
    set a i ai := a.set (toFin i) ai

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
