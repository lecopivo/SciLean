import Lean
import SciLean.Functions.FFT

open SciLean
open Lean Widget
open Lean.Json

instance : ToJson (Vec2 Float) where
  toJson v := Json.mkObj [("x", toJson v.x), ("y", toJson v.y)]

def Array.intro {n α} (f : Fin n → α) : Array α := Id.run do
  let mut a : Array α := Array.mkEmpty n
  for i in [0:n] do
    a := a.push (f ⟨i, sorry⟩)
  a

def generateData := Id.run do

  let n := 6

  let steps := 2^n
  let mut data : Array (Array (Vec2 Float)) := Array.mkEmpty steps

  for waveNumber in [0:2^n] do

    let wave : ℝ^{2^n, 2} := introElem λ (i,j) => 

      let θ := 2 * Math.pi * waveNumber * (i.1.toReal / 2^n)
      if j = 0 then
        Math.cos θ
      else
        Math.sin θ 

    let wave' := FFT wave

    data := data.push (Array.intro (λ i => ⟨i.1.toFloat, wave'[i,0].toFloat⟩))

  data


@[widget]
def helloWidget : UserWidgetDefinition where
  name := "Hello"
  javascript := include_str "." / "plot.js"

#widget helloWidget (Json.mkObj [
  ("data", toJson generateData),
  ("useTimer", true),
  ("yDomain", toJson [0, 1])
])
