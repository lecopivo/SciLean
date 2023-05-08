import ProofWidgets.Component.InteractiveSvg
import ProofWidgets.Component.HtmlDisplay
import examples.Ballistic

open Lean
open ProofWidgets Svg Jsx

open SciLean

def frame : Frame where
  xmin := -1
  ymin := -1
  xSize := 2
  width := 400
  height := 400


structure State where
  v : ℝ×ℝ
deriving ToJson, FromJson

local instance {frame : Frame} : CoeHead (Point frame) (ℝ^{2}) where
  coe p := ⊞ i, if i = 0 then ⟨p.toAbsolute.1⟩ else ⟨p.toAbsolute.2⟩

local instance {frame : Frame} : CoeTail (ℝ^{2}) (Point frame) where
  coe x := .abs x[0].toFloat x[1].toFloat

local instance : Coe (ℝ^{2}) (ℝ×ℝ) where
  coe x := (x[0],x[1])

local instance : Coe (ℝ×ℝ) (ℝ^{2}) where
  coe x := ⊞ i, if i = 0 then x.1 else x.2

def isvg : InteractiveSvg State where
  init := { v := 0 }

  frame := frame

  update time Δt action mouseStart mouseEnd selected getData state :=

    if let .some mouseEnd := mouseEnd then
      let target : ℝ^{2} := mouseEnd
      let newVel := aimStep target state.v
      { v := newVel }
    else
      state

  render time mouseStart mouseEnd state :=
    {
      elements := Id.run do
        let n : ℕ := 50
        let Δt := (1:ℝ)/n

        let mut pts : Array (Point frame) := .mkEmpty (n+1)

        let trajectory := shotTrajectoryPoints 50 1 state.v

        pts := pts.append (trajectory.map fun xv => xv.1)

        let mut elems : Array (Element frame) := #[]

        if let .some target := mouseEnd then
          elems := elems.push <| Svg.circle target (.px 5) |>.setFill (0.9,0.1,0.1)
        
        elems := elems.push <|
          Svg.line (.abs 0 0) ((0.1:ℝ)•state.v) |>.setStroke (0.9,0.8,0.2) (.px 2)

        elems := elems.push <| 
          Svg.polyline pts |>.setStroke (0.8,0.8,0.8) (.px 2)

        elems
    }


open Server RequestM in
@[server_rpc_method]
def updateSvg (params : UpdateParams State) : RequestM (RequestTask (UpdateResult State)) := isvg.serverRpcMethod params

-- TODO: the tsx file is pretty broken
@[widget_module]
def SvgWidget : Component (UpdateResult State) where
  javascript := include_str ".." / "lake-packages" / "proofwidgets" / "build" / "js" / "interactiveSvg.js"

def init : UpdateResult State := {
  html := Html.ofTHtml <div>Init!!!</div>,
  state := { state := isvg.init
             time := 0
             selected := none
             mousePos := none
             idToData := isvg.render 0 none none isvg.init |>.idToDataList}
}

#html <SvgWidget html={init.html} state={init.state}/>
