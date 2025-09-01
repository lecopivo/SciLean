import ProofWidgets.Component.InteractiveSvg
import ProofWidgets.Component.HtmlDisplay
import SciLean.Data.Mesh.Prism

open Lean
open ProofWidgets Svg Jsx

open SciLean

def frame : Frame where
  xmin := -1
  ymin := -10
  xSize := 20
  width := 1000
  height := 600

abbrev State := Nat

def rotate2d (x : ℝ×ℝ) (θ : ℝ) : ℝ×ℝ :=
  let cθ := θ.cos
  let sθ := θ.sin
  (cθ * x.1 + sθ * x.2, - sθ * x.1 + cθ * x.2)

def SciLean.PrismRepr.Space.project2d {P : PrismRepr} (x : P.Space) : ℝ×ℝ :=
let θ := - Real.pi * (1 - (1/2 : ℝ)^(P.dim-1))
let s : ℝ := 1.5^(- (P.dim - 2 : Nat))
match P, x with
| .point, 0 => (0,0)
| .cone _, (t,x) =>
  x.project2d + s • rotate2d (t,0) θ
| .prod _ _, (x, y) =>
  s • (rotate2d x.project2d θ) + y.project2d

instance : Coe (ℝ × ℝ) (Svg.Point f) := ⟨λ (x,y) => .abs x.toFloat y.toFloat⟩


def SciLean.Prism.toSvg (P : Prism) (shift := ((0,0) : ℝ×ℝ))  : Array (Svg.Element f) := Id.run do
  let mut elems : Array (Element f) := #[]

  for edge in P.faces (some 1) do
    let edge' : Inclusion Prism.segment P := ⟨edge.1, sorry_proof, sorry_proof⟩
    let pt0 := edge'.comp Prism.segment.point0 |>.toFace |>.position' |>.project2d
    let pt1 := edge'.comp Prism.segment.point1 |>.toFace |>.position' |>.project2d
    elems := elems.push <|
      Svg.line (pt0 + shift) (pt1 + shift)
        |>.setStroke (0.3,0.3,0.3) (.px 1)
        |>.setId edge.repr.toString

  for point in P.faces (some 0) do
    let pt := point.position'.project2d
    elems := elems.push <|
      Svg.circle (pt + shift) (.px 5)
        |>.setStroke (0.2,0.2,0.2) (.px 1)
        |>.setFill (0.4,0.4,0.4)
        |>.setId point.repr.toString

  elems


def isvg : InteractiveSvg State where
  init := 0

  frame := frame

  update time Δt action mouseStart mouseEnd selected getData state := state

  render time mouseStart mouseEnd state :=
    {
      elements := Id.run do
        let P := Prism.point.cone.cone


        let mut elems : Array (Element frame) := #[]

        elems := elems.push <|
          Svg.polygon #[(.px 0 0), (.px frame.width 0), (.px frame.width frame.height), (.px 0 frame.height)]
            |>.setFill (1.0,1.0,1.0)

        for dim in fullRange (Fin 5) do
          for i in fullRange (Fin (Prism.prismCount dim.1)) do
            let P := Prism.prismFromFin dim i
            let shift : ℝ×ℝ := (2*i.1, - 2*dim.1)
            elems := elems.append (P.toSvg shift)

            let dim' := 2
            if dim' ≤ dim then
              let fId : Fin (P.faceCount dim') := ⟨(0.002*time).toUSize.toNat % (P.faceCount dim'), sorry_proof⟩
              let f := Face.fromFin P _ fId
              let mut pts : Array (Point frame) := #[]
              for point in f.faces (some 0) do
                let point := f.comp point -- make the point w.r.t to P
                pts := pts.push <| point.position'.project2d + shift

              -- deal with squares
              if dim'=2 && pts.size=4 then
                pts := pts.swap! 0 1

              elems := elems.push <|
                Svg.polygon pts
                  |>.setFill (0.3,0.6,0.7)
                  |>.setStroke (0.2,0.8,0.8) (.px 2)


        elems
    }

open Server RequestM in
@[server_rpc_method]
def updateSvg (params : UpdateParams (State)) : RequestM (RequestTask (UpdateResult (State))) := isvg.serverRpcMethod params


@[widget_module]
def SvgWidget : Component (UpdateResult (State)) where
  javascript := include_str ".." / "lake-packages" / "proofwidgets" / "build" / "js" / "interactiveSvg.js"

def init : UpdateResult (State) := {
  html := Html.ofTHtml <div>Init!!!</div>,
  state := { state := isvg.init
             time := 0
             selected := none
             mousePos := none
             idToData := isvg.render 0 none none isvg.init |>.idToDataList}
}

#html <SvgWidget html={init.html} state={init.state}/>
