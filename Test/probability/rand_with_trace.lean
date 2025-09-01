import SciLean.Probability.RandWithTrace
import SciLean.Analysis.Scalar.FloatAsReal

open SciLean Rand MeasureTheory


/--
info: ((normal 0.0 1.0).sample `v1).bind (fun x => return' x)
  ⋯ : RandWithTrace Float (Trace.single `v1 Float ++ Trace.nil) (Float × Unit)
-/
#guard_msgs in
#check (let x <~ sample (normal (0.0:Float) 1.0) `v1; return' x)


/-- info: fun x => gaussian 0.0 1.0 x.1 : Float × Unit → Float -/
#guard_msgs in
#check ((let x <~ sample (normal (0.0:Float) 1.0) `v1; return' x).traceRand.pdf Float)
  rewrite_by
    simp[trace_bind_pdf]


def tt :=
    (let (_,x) <~ forLoop (init:=(0.0,#[])) (n:=50) (fun i (x,xs) =>
                    let x' <~ sample (normal x 1.0) `v1
                    return' (x', xs.push x'))
     let y <~ sample (normal x.1.sum 1.0) `y
     return' y)


/--
info: tt :
  RandWithTrace Float ((Trace.single `v1 Float ++ Trace.nil).array 50 ++ (Trace.single `y Float ++ Trace.nil))
    (Vector (Float × Unit) 50 × Float × Unit)
-/
#guard_msgs in
#check tt


-- /--
-- info: fun x =>
--   pdf Float
--       (forLoop (fun i x => ((normal x.1 1.0).sample `v1).bind (fun x' => return' (x', x.2.push x')) tt.proof_1)
--           (0.0, #[]) 50).traceRand
--       volume x.1 *
--     gaussian
--       ((forLoop (fun i x => ((normal x.1 1.0).sample `v1).bind (fun x' => return' (x', x.2.push x')) tt.proof_1)
--                   (0.0, #[]) 50).map
--               x.1).2.toList.sum
--       1.0 x.2.1 : ArrayN (Float × Unit) 50 × Float × Unit → Float
-- -/
-- #guard_msgs in
-- #check (tt.traceRand.pdf Float) rewrite_by
--   unfold tt
--   simp


/-- info: fun x => gaussian 0.0 1.0 x.1 * gaussian x.1 1.0 x.2.1 : Float × Float × Unit → Float -/
#guard_msgs in
#check (
    (let x <~ sample (normal (0.0:Float) 1.0) `v1
     let y <~ sample (normal x 1.0) `v2
     return' y).traceRand.pdf Float)
  rewrite_by
    simp


/-- info: fun x => gaussian 0.0 1.0 x.1 : Float × Unit → Float -/
#guard_msgs in
#check ((let x <~ sample (normal (0.0:Float) 1.0) `v1;
         return' x).traceRand.pdf Float)
  rewrite_by
    simp[trace_bind_pdf]


/--
info: ((normal 0.0 1.0).sample `v1).bind (fun x => return' x)
  ⋯ : RandWithTrace Float (Trace.single `v1 Float ++ Trace.nil) (Float × Unit)
-/
#guard_msgs in
#check let x <~ sample (normal (0.0:Float) 1.0) `v1;
       return' x


def temperature :=
    (let tempLower := 2.0
     let tempUpper := 4.0
     let invCR := 0.1
     let tempA := 3.0
     let rpRate := 5.0
     let sigma1 := 1.0
     let sigma0 := 2.0
     let sqrtTimeStep := 0.1

     let aconInit := false
     let acons := #[aconInit]
     let tempInit <~ sample (normal 2.0 0.001) `temp_init
     let temps := #[tempInit]
     let dataInit <~ sample (normal tempInit 1.0) `data_init
     let data := #[dataInit]

     let (_,_,temps,acons,data) <~
       forLoop (init:=(tempInit,aconInit,temps,acons,data)) (n:=20)
         (fun i (tempPrev,aconPrev,temps,acons,data) =>
            let m :=
              if tempPrev < tempLower then false
              else if tempPrev > tempUpper then true
              else aconPrev

            let aconNoise <~ sample (normal m.toNat.toFloat 0.001) `acon_noise
            let acon := if aconNoise > 0.5 then true else false

            let b := invCR * (tempA - (tempPrev + acon.toNat.toFloat * rpRate))
            let s := if aconNoise > 0.5 then sigma1 else sigma0

            let temp <~ sample (normal (tempPrev + b) (s * sqrtTimeStep)) `temp

            let dataPoint <~ sample (normal temp 1.0) `data

            return' (tempPrev,aconPrev,temps.push temp,acons.push acon,data.push dataPoint))
     return' ())
