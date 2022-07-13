import SciLean.Data.NFloatArray

namespace SciLean

-- TODO Maybe add specialized versions for small values of `n`

-- just NFloatArray with different type signatures
def NRealArray (n : Nat) := NFloatArray n

namespace NRealArray

  def get {n} (a : NRealArray n) (i : Fin n) : ℝ := ⟨a.1.get (a.2 ▸ i)⟩
  def getOp {n} (self : NRealArray n) (idx : Fin n) : ℝ := self.get idx

  def set {n} (a : NRealArray n) (i : Fin n) (ai : ℝ) : NRealArray n :=
    ⟨a.1.set (a.2 ▸ i) ai.1, sorry⟩

  def intro {n} (f : Fin n → ℝ) : NRealArray n := Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in [0:n] do
      let i := ⟨i, sorry⟩
      x := x.push (f i).1
    ⟨x, sorry⟩

  instance : GetElem (NRealArray n) (Fin n) ℝ (λ _ _ => True) where
    getElem a i _ := a.get i
  instance : FunType (NRealArray n) (Fin n) ℝ where
    ext := sorry

  instance [Enumtype ι] : GetElem (NRealArray (numOf ι)) ι ℝ (λ _ _ => True) where
    getElem a i _ := a.get (toFin i)
  instance [Enumtype ι] : FunType (NRealArray (numOf ι)) ι ℝ where
    ext := sorry

  open FunType

  instance : SetElem (NRealArray n) (Fin n) ℝ where
    setElem a i ai := a.set i ai
  instance : HasSet (NRealArray n) where
    toFun_set_eq  := sorry
    toFun_set_neq := sorry

  instance [Enumtype ι] : SetElem (NRealArray (numOf ι)) ι ℝ where
    setElem a i ai := a.set (toFin i) ai
  instance [Enumtype ι] : HasSet (NRealArray (numOf ι)) where
    toFun_set_eq  := sorry
    toFun_set_neq := sorry

  instance : HasIntro (NRealArray n) where
    intro f := intro f

    toFun_intro := sorry

  -- TODO: This can can a faster implementation using `Iterable.next`
  instance [Enumtype ι] : HasIntro (NRealArray (numOf ι)) where
    intro f := intro (λ i => f (fromFin i))

    toFun_intro := sorry

end NRealArray

