import SciLean.Core

namespace SciLean


def extend1DFinConst {α} (a : α) (f : Fin n → α) (i : Int) : α :=
  if i ≥ 0 && i < n then
    let i : Fin n := ⟨i.toNat, sorry_proof⟩
    f i
  else
    a


def extend1DFinStreak {α} [Inhabited α] (f : Fin n → α) (i : Int) : α :=
  if n = 0 then
    default
  else
    if i < 0 then
      f ⟨0, sorry_proof⟩
    else if i≥n then
      f ⟨n-1, sorry_proof⟩
    else
      f ⟨i.toNat, sorry_proof⟩


def extend1DIdxStreak {α} [Inhabited α] (f : Idx n → α) (i : Int) : α :=
  if n = 0 then
    default
  else
    if i < 0 then
      f ⟨0, sorry_proof⟩
    else if i≥n.toNat then
      f ⟨n-1, sorry_proof⟩
    else
      f ⟨i.toNat.toUSize, sorry_proof⟩

      
def extend1DFinPeriodic {α} (a : α) (f : Fin n → α) (i : Int) : α :=
  if i ≥ 0 && i < n then
    let i : Fin n := ⟨i.toNat, sorry_proof⟩
    f i
  else
    a
