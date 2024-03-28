import ProofWidgets.Component.InteractiveSvg
import ProofWidgets.Component.HtmlDisplay
import examples.WaveEquation

open Lean
open ProofWidgets Svg Jsx

open SciLean

abbrev State (n : Nat) := Float^[n] × Float^[n]


instance : ToJson (DataArrayN Float (Fin n)) where
  toJson := fun x =>
    let x' := Array.ofFn (fun i => x[i])
    toJson x'

instance : FromJson (DataArrayN Float (Fin n)) where
  fromJson? := fun json => do
    let x' : Array Float ← fromJson? json
    return (⊞ (i : Fin n) => x'[i.1]!)

def frame : Frame where
  xmin := -1
  ymin := -1
  xSize := 2
  width := 400
  height := 400


def isvg (n) : InteractiveSvg (State n) where
  init := (⊞ (i : Fin n) => (0:Float), -- 0 * Float.sin (2*RealScalar.pi*(i.toFloat)/40),
           ⊞ (i : Fin n) => (0:Float))

  frame := frame

  update time Δt action mouseStart mouseEnd selected getData state := Id.run do
    let m : Float := 0.1
    let k : Float := 50000.0
    -- convert time to seconds
    let time : Float := time/1000
    let Δt : Float := Δt/1000
    let mut (x,v) := state
    if let .some pos := mouseEnd then
      if action.kind == .mousedown then
        let θ := Float.atan2 pos.toAbsolute.1 pos.toAbsolute.2
        for i in IndexType.univ (Fin n) do
          let θ' := (2 * (RealScalar.pi : Float) * i.1) / n
          let θ' := if θ' ≤ RealScalar.pi then θ' else θ' - 2*RealScalar.pi
          let w := min (θ - θ').abs (θ - θ' + 2*RealScalar.pi).abs
          x[i] += Float.exp (- 50*w^2)
    solver m k (1,()) time (time + Δt) (x,v)

  render time mouseStart mouseEnd state :=
    {
      elements := Id.run do
        let mut pts : Array (Point frame) := .mkEmpty n
        -- let mut qts : Array (Point frame) := .mkEmpty n.toNat
        let Δθ := 2*(RealScalar.pi : Float) / n
        for i in IndexType.univ (Fin n) do
          let θ := i.1 * Δθ
          let r := 0.5 + 0.2*state.1[i]
          pts := pts.push (.abs (r*θ.cos) (r*θ.sin))
          -- qts := qts.push (.abs (-frame.xmin + (i.1.toNat.toFloat/n.toNat.toFloat)*frame.xSize) (0.3*state.1[i].toFloat))
        #[Svg.circle (.abs 0 0) (.abs 2) |>.setFill (1.0,1.0,1.0),
          Svg.polygon pts |>.setFill (0.95,0.95,0.95) |>.setStroke (0.2,0.2,0.2) (.px 1)]-- ,
          -- Svg.polyline qts |>.setStroke (0.2,0.8,0.2) (.px 1)]
    }



open Server RequestM in
@[server_rpc_method]
def updateSvg (params : UpdateParams (State 100)) : RequestM (RequestTask (UpdateResult (State 100))) := (isvg 100).serverRpcMethod params

-- TODO: the tsx file is pretty broken
@[widget_module]
def SvgWidget : Component (UpdateResult (State 100)) where
  javascript := include_str ".." / ".lake" / "packages" / "proofwidgets" / ".lake" / "build" / "js" / "interactiveSvg.js"

def init : UpdateResult (State 100) := {
  html := <div>Init!!!</div>,
  state := { state := (isvg 100).init
             time := 0
             selected := none
             mousePos := none
             idToData := (isvg 100).render 0 none none (isvg 100).init |>.idToDataList}
}

#html <SvgWidget html={init.html} state={init.state}/>
