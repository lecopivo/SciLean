import Lean
import SciLean.PhysicalSystems.Wave

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

def generateData : Json := Id.run do
  let substeps := 1
  let m := 1.0
  let k := 100000.0

  let N : Nat := 100
  have h : Nonempty (Fin N) := sorry

  let evolve := (solver (n:=N) m k substeps).val

  let t := 1.0
  let x₀ : ℝ^{N} := .intro λ (i : Fin N) => (Math.sin ((i.1 : ℝ)/10))
  let p₀ : ℝ^{N} := .intro λ i => (0 : ℝ)
  let mut (x,p) := (x₀, p₀)

  let steps := 10
  let mut data : Array (Array (Vec2 Float)) := Array.mkEmpty steps
  
  for i in [0:steps] do
  
    (x, p) := evolve 0.1 (x, p)
    
    data := data.push (Array.intro (λ i => ⟨i.1.toFloat/ N.toFloat, x[i].toFloat⟩))

  toJson data
  -- data.map (λ d => d.map (

#eval generateData


@[widget]
def helloWidget : UserWidgetDefinition where
  name := "Hello"
  javascript := "
    import * as React from 'react';
    export default function(props) {
      const name = (props.name || 'world') + ' ' + props.dog
      return React.createElement('p', {}, name + '!')
    }"

#widget helloWidget .null

#widget helloWidget (Json.mkObj [("name", "Tomas"), ("dog", "labrador")])

-- def main : IO Unit := do

--   let substeps := 1
--   let m := 1.0
--   let k := 100000.0

--   let N : Nat := 100
--   have h : Nonempty (Fin N) := sorry

--   let evolve := (solver (n:=N) m k substeps).val

--   let t := 1.0
--   let x₀ : (ℝ^{N}) := .intro λ (i : Fin N) => (Math.sin ((i.1 : ℝ)/10))
--   let p₀ : (ℝ^{N}) := .intro λ i => (0 : ℝ)
--   let mut (x,p) := (x₀, p₀)

--   for i in [0:1000] do
  
--     (x, p) := evolve 0.1 (x, p)

--     let M : Nat := 20
--     for (m : Nat) in [0:M] do
--       for (n : Nat) in [0:N] do
        
--         let xi := x[!n]
--         if (2*m - M)/(M : ℝ) - xi < 0  then
--           IO.print "x"
--         else
--           IO.print "."

--       IO.println ""


-- -- #eval main
