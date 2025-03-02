import SciLean

import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets


open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

macro (priority:=high) A:term noWs "[" i:term "," ":" "]" : term => `(MatrixType.row $A $i)
macro (priority:=high) A:term noWs "[" ":" "," j:term "]" : term => `(MatrixType.col $A $j)

axiom unsafeNonzero {α} [Zero α] (a : α) : a ≠ 0

macro "unsafeAD" : tactic =>
  `(tactic| (intros; simp only [not_false_eq_true, ne_eq, unsafeNonzero]))


open Lean Meta
instance : MonadLift Tactic.DataSynth.DataSynthM SimpM where
  monadLift e := do
    let disch? := (← Simp.getMethods).discharge?
    -- discharge? : Expr → SimpM (Option Expr) := fun _ => return none
    let r := e { discharge := disch? } (← ST.mkRef {}) (← ST.mkRef {})
    r


theorem revFDeriv_from_hasRevFDeriv {K} [RCLike K]
  {X} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {f : X → Y} {f'} (hf : HasRevFDeriv K f f') :
  revFDeriv K f = f' := sorry_proof


open Lean Meta in
/-- Compute `revFDeriv R f` with calling data_synth on `HasRevFDeriv R f ?f'`. -/
simproc_decl revFDeriv_simproc (revFDeriv _ _) := fun e => do

  -- get field and function to differentiate
  let K := e.getArg! 0
  let f := e.appArg!

  -- craft `HasRevFDeriv K f ?f'`
  let goal ← mkAppM ``HasRevFDeriv #[K,f]
  let (xs,_,_) ← forallMetaTelescope (← inferType goal)
  let f' := xs[0]!
  let goal := goal.app f'

  -- extract data_synth goal
  let .some goal ← Tactic.DataSynth.isDataSynthGoal? goal
    | throwError "something went really wrong"

  -- run data_synth
  let .some r ← Tactic.DataSynth.dataSynth goal
    | return .continue

  let f'' := r.xs[0]!
  let prf ← mkAppM ``revFDeriv_from_hasRevFDeriv #[r.proof]
  -- IO.println (← ppExpr (← inferType prf))

  -- let eq ← mkEq e f''
  -- let prf ← mkSorry eq false

  return .visit { expr := f'', proof? := prf }


set_default_scalar Float
open Scalar
example : (<∂ x : Float, x) = fun x => (x, fun dx => dx) := by simp[revFDeriv_simproc]
example : (<∂ x : Float, x*x) = fun x => (x*x, fun dx => x*dx+x*dx) := by simp[revFDeriv_simproc]
example : (<∂ x : Float, exp x) = fun x => (exp x, fun dx => dx*exp x) := by simp[revFDeriv_simproc]

def H {n} (m : Fin n → Float) (x p : Float^[n,2]) : Float :=
  (∑ i, (1/(2*m i)) * ‖p[i,:]‖₂²)
  -
  (∑ (i : Fin n) (j : Fin i.1),
    let j := j.castLT (by omega)
    (m i*m j) * ‖x[i,:] - x[j,:]‖₂⁻¹)



#check (<∂ x':=(⊞[1.0,2.0,3.0]:Float3), ‖x'‖₂⁻¹) rewrite_by
  unfold fgradient
  lsimp (disch:=unsafeAD) only [simp_core,revFDeriv_simproc]

variable (x p : Float^[n,3]) (ε : Float)

-- set_option trace.Meta.Tactic.data_synth true in
-- #check (<∂ x':=x, ∑ i j, ‖x'[i,:] - x'[j,:]‖₂⁻¹) rewrite_by
--   unfold fgradient
--   lsimp (disch:=unsafeAD) only [simp_core, revFDeriv_simproc]

-- #check (<∂ x':=x, H (fun _ => 1) x' p) rewrite_by
--   unfold fgradient H
--   lsimp (disch:=unsafeAD) only [simp_core, revFDeriv_simproc]

-- #check (<∂ p':=p, H (fun _ => 1) x p') rewrite_by
--   unfold fgradient H
--   lsimp (disch:=unsafeAD) only [simp_core, revFDeriv_simproc]


-- #check odeSolve.arg_x₀.revFDeriv_rule


approx solver (m : Fin n → Float)
  := odeSolve (fun (t : Float) (x,p) => ( ∇ (p':=p), H m x  p',
                                         -∇ (x':=x), H m x' p))
by
  -- Unfold Hamiltonian and compute gradients
  unfold H fgradient
  lsimp (disch:=unsafeAD) only [simp_core,revFDeriv_simproc]

  -- Apply RK4 method
  simp_rw (config:={zeta:=false}) [odeSolve_fixed_dt rungeKutta4 sorry_proof]

  -- todo: make approx_limit ignore leading let bindings
  approx_limit n sorry_proof



#eval! solver (fun _ : Fin 2 => 1) (10,()) 0 0.7
         (⊞[-1.0,0;1.0,0],⊞[0.0,-1.0;0,1.0])


def generateData (m : ℕ) : Float^[2,2]^[m] := Id.run do

  let mut data : Float^[2,2]^[m] := 0
  let Δt := 0.01

  -- initial state
  let mut x := ⊞[-1.0, 0.0;
                  1.0, 0.0]

  let mut p := ⊞[ 0.0,-0.3;
                  0.0, 0.3]

  for h : i in [0:m] do
    let i : Fin m := ⟨i, sorry_proof⟩
    data[i] := x
    (x,p) := solver 1 (1,()) 0 Δt (x,p)

  return data


open ProofWidgets Svg

private def frame : Frame where
  xmin   := -2
  ymin   := -2
  xSize  := 4
  width  := 400
  height := 400

open IndexType
instance {I} [IndexType I] : ToJson (Float^[I]) where
  toJson x := toJson (Array.ofFn (fun i => x[fromFin i]))

instance {I} [IndexType I] : FromJson (Float^[I]) where
  fromJson? j :=
    match fromJson? (α:=Array Float) j with
    | Except.error e => Except.error e
    | Except.ok data =>
      Except.ok (⊞ (i : I) => data[toFin i]!)


instance (f : Frame) : Coe (Float^[2]) (Point f) := ⟨fun x => .abs x[0] x[1]⟩

private def svg : Svg frame :=
  let data := generateData 1000

  { elements :=
      #[polyline (Array.ofFn (fun i => data[i][0,:])) |>.setStroke (0.8,0.8,0.2) (.px 1) ,
        polyline (Array.ofFn (fun i => data[i][1,:])) |>.setStroke (0.2,0.8,0.8) (.px 1) ] }

#html svg.toHtml
