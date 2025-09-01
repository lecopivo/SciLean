import SciLean

open SciLean Scalar Lean ToJson FromJson

set_option pp.deepTerms true
set_option pp.proofs false

section RowColSimps

variable {X : Type*} [PlainDataType X]
  {I nI} [IndexType I nI]
  {J nJ} [IndexType J nJ]

@[simp, simp_core]
theorem getElem_row (A : X^[I,J]) (i : I) (j : J) : (A.row i)[j] = A[i,j] := sorry_proof

@[simp, simp_core]
theorem getElem_col (A : X^[I,J]) (i : I) (j : J) : (A.col j)[i] = A[i,j] := sorry_proof

end RowColSimps

set_default_scalar Float

open Scalar in
def sigmoid {R} [RealScalar R] (x : R) : R := 1 / (1 + exp (-x))

abbrev_data_synth sigmoid in x : HasRevFDeriv R by
  unfold sigmoid
  data_synth (disch:=sorry_proof) => enter[3]; simp; to_ssa; to_ssa; lsimp

abbrev_data_synth sigmoid in x : HasRevFDerivUpdate R by
  unfold sigmoid
  data_synth (disch:=sorry_proof) => enter[3]; simp; to_ssa; to_ssa; lsimp


open Scalar in
abbrev_data_synth Scalar.tanh in x : HasRevFDeriv K by
  conv => enter[3]; assign (fun x : K =>
    let y := tanh x
    (y, fun dy => dy*(1 - y^2)))
  sorry_proof



open ArrayOps in
def lstmModel {d : ℕ}
              (weight: Float^[4,d])
              (bias: Float^[4,d])
              (hidden: Float^[d])
              (cell: Float^[d])
              (input: Float^[d]) : Float^[d] × Float^[d] :=
  let forget  := input  |> mapIdxMonoAcc (fun _ (wi,bi) xi => sigmoid (wi*xi + bi)) (fun i => (weight[0,i],bias[0,i]))
  let ingate  := hidden |> mapIdxMonoAcc (fun _ (wi,bi) xi => sigmoid (wi*xi + bi)) (fun i => (weight[1,i],bias[1,i]))
  let outgate := input  |> mapIdxMonoAcc (fun _ (wi,bi) xi => sigmoid (wi*xi + bi)) (fun i => (weight[2,i],bias[2,i]))
  let change  := hidden |> mapIdxMonoAcc (fun _ (wi,bi) xi =>    tanh (wi*xi + bi)) (fun i => (weight[3,i],bias[3,i]))
  let cell2   := mapIdxMonoAcc (fun _ (a,b,c) d => a*b + c*d) (fun i => (cell[i],forget[i],ingate[i])) change
  let hidden2 := mapIdxMonoAcc (fun _ a b => tanh a * b) (cell[·]) outgate

  (hidden2, cell2)

set_option maxRecDepth 1000000

def_data_synth lstmModel in weight bias hidden cell input : HasRevFDeriv Float by
  unfold lstmModel; dsimp -zeta only
  data_synth => enter[3]; lsimp

open VectorType MatrixType in
def lstmPredict {slen d : ℕ}
                (mainParams: (Float^[4,d])^[slen,2])
                (extraParams: Float^[3,d])
                (state: (Float^[d])^[slen,2])
                (input: Float^[d]) : Float^[d] × Float^[d]^[slen,2] :=
  let x₀ := input.rmap2 (·*·) (extraParams.row 0)
  let state₀ : (Float^[d])^[slen,2] := 0

  let' (state',x') := IndexType.fold .full (init:=(state₀,x₀))
    (fun (i : Idx slen) sx =>
      let' (s,x) := sx
      let' (h,c) := lstmModel mainParams[i,0] mainParams[i,1] state[i,0] state[i,1] x
      let s := setElem s (i,(0:Idx 2)) h .intro
      let s := setElem s (i,(1:Idx 2)) c .intro
      (s,h))

  let v' := x'.rmap2 (·*·) (extraParams.row 1) + (extraParams.row 2)
  (v', state')


def_data_synth lstmPredict in mainParams extraParams state : HasRevFDeriv Float by
  unfold lstmPredict; --dsimp -zeta
  data_synth => enter[3]; lsimp


open VectorType in
abbrev_data_synth Scalar.log in x : HasRevFDeriv K by
  conv => enter[3]; assign (fun x => (Scalar.log x, fun dx : K => dx/x))
  sorry_proof

abbrev_data_synth Scalar.log in x : HasRevFDerivUpdate K by
  conv => enter[3]; assign (fun x => (Scalar.log x, fun (dx : K) dx' => dx' + dx/x))
  sorry_proof


open VectorType MatrixType in
def lstmObjective {slen lenSeq d : ℕ}
                  (mainParams : (Float^[4,d])^[slen,2])
                  (extraParams : Float^[3,d])
                  (state : (Float^[d])^[slen, 2])
                  (sequence : Float^[d]^[lenSeq]) : Float :=
  -- state : [stlen][2][d]f64
  let' (_a, total) := IndexType.fold .full (init:=(state, (0:Float)))
    fun (i : Idx (lenSeq - 1)) st =>
      let' (oldState, oldTotal) := st
      let' (y_pred, newState) := lstmPredict mainParams extraParams oldState sequence[⟨i.1,sorry_proof⟩]
      -- y_pred: DV [d]f64, newState: DM
      let tmp_sum := ∑ᴵ i, (exp y_pred[i])
      let tmp_log := - Scalar.log (tmp_sum + 2.0)
      let ynorm := y_pred.scalAdd 1 tmp_log
      let newTotal := oldTotal + (⟪sequence[⟨i.1 + 1,sorry_proof⟩], ynorm⟫)
      (newState, newTotal)

  let count := d * (lenSeq - 1) |>.toFloat
  (-total * count⁻¹)


abbrev_data_synth lstmObjective in mainParams extraParams : HasRevFDeriv Float by
  unfold lstmObjective; --dsimp -zeta
  data_synth => enter[3]; lsimp



-- set_option linter.unusedVariables false in
-- def lstmJacobian {slen lenSeq d : ℕ}
--                  (mainParams : (Float^[4,d])^[slen,2])
--                  (extraParams : Float^[3,d])
--                  (state : (Float^[d])^[slen, 2])
--                  (sequence : Float^[d]^[lenSeq])
--   {f'} (deriv : HasRevFDeriv Float (fun (x,y) => lstmObjective x y state sequence) f')
--   {grad} (simp : grad = (f' (mainParams,extraParams)).2 1) := grad


set_option linter.unusedVariables false in
def lstmJacobian {slen lenSeq d : ℕ}
                 (mainParams : (Float^[4,d])^[slen,2])
                 (extraParams : Float^[3,d])
                 (state : (Float^[d])^[slen, 2])
                 (sequence : Float^[d]^[lenSeq]) :=
  ((<∂ xy:=(mainParams,extraParams), lstmObjective xy.1 xy.2 state sequence).2 1)
  rewrite_by
    autodiff


def _root_.Float.toInt (x : Float) : Int :=
  if 0 ≤ x then
    x.toUInt64.toNat
  else
    - Int.ofNat (-x).toUInt64.toNat

def _root_.Int.toFloat (x : Int) : Float :=
  if 0 ≤ x then
    x.toNat.toFloat
  else
    - (-x).toNat.toFloat

instance (priority:=high+1) : ToString Float := ⟨fun x => Id.run do
  if ¬x.isFinite then
    toString x
  else if x.abs == 0 then
    toString x
  else
  let mut exponent := (x.abs).log10.toInt
  let mut mantisa := x / (10.0^exponent)
  s!"{mantisa}e{exponent}"⟩


def main (args : List String) : IO Unit := do

   let seed := (args.get? 0 |>.getD "0").toNat? |>.getD 0

   let slen := 4000
   let lenSeq := 6
   let d := 14
   IO.setRandSeed seed
   let mainParams : (Float^[4,d])^[slen,2] :=
     ⊞ (_ : Idx slen × Idx 2) => ⊞ (_ : Idx 4 × Idx d) => (← (Rand.uniform (X:=Float) (Set.Icc 0 1)).get)
   let extraParams : Float^[3,d] :=
     ⊞ (_ : Idx 3 × Idx d) => (← (Rand.uniform (X:=Float) (Set.Icc 0 1)).get)
   let state : (Float^[d])^[slen, 2] :=
     ⊞ (_ : Idx slen × Idx 2) => ⊞ (_ : Idx d) => (← (Rand.uniform (X:=Float) (Set.Icc 0 1)).get)
   let sequence : Float^[d]^[lenSeq] :=
     ⊞ (_ : Idx lenSeq) => ⊞ (_ : Idx d) => (← (Rand.uniform (X:=Float) (Set.Icc 0 1)).get)

   let grad := lstmJacobian mainParams extraParams state sequence

   let h := hash (grad.1.1.1, grad.2.1.1)
   IO.println h
