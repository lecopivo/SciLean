import SciLean

namespace SciLean

open Rand MeasureTheory

variable {R} [RealScalar R] [MeasureSpace R]

def model1 :=
  let x ~ uniformI (R:=R)
  let y ~ flip x

example (r : R) :
    (model1.conditionFst r)
    =
    Rand.flip r := by
  unfold model1
  simp

example (r : R) :
    ((model1 (R:=R)).pdf R (volume.prod .count))
    =
    (fun xy =>
      let x := (xy.1 ⊔ 0) ⊓ 1
      (if 0 < xy.1 ∧ xy.1 < 1 then 1 else 0)
      *
      if xy.2 = true then x else 1 - x) := by
  unfold model1
  simp only [ftrans_simp]


def model2 :=
  let v ~ normal (0:R) 5
  if v > 0 then
    let obs ~ normal (1:R) 1
  else
    let obs ~ normal (-2:R) 1


example :
    (model2 (R:=R)).pdf R
    =
    (fun (x,y) =>
      if 0 < x then
        gaussian 0 5 x * gaussian 1 1 y
      else
        gaussian 0 5 x * gaussian (-2) 1 y) := by

  unfold model2
  simp only [ftrans_simp, Tactic.if_pull] -- if_pull uses sorry right now


example (v : R) :
    ((model2 (R:=R)).conditionFst v).pdf R
    =
    (fun y =>
      if 0 < v then
        gaussian 1 1 y
      else
        gaussian (-2) 1 y) := by

  unfold model2
  simp only [ftrans_simp, Tactic.if_pull] -- if_pull uses sorry right now
