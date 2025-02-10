import SciLean

open SciLean

#check FloatVector

macro "Float^[" n:term "]" : term => `(FloatVector (Fin $n))

open VectorType

variable
  {R} [RealScalar R]
  {X} [NormedAddCommGroup X] [AdjointSpace R X]
  {Y} [NormedAddCommGroup Y] [AdjointSpace R Y]

def evalGrad (f : X → R) {f'} (hf : HasRevFDeriv R f f') (x : X) : X := (f' x).2 1

/--
info: [0.000000, 1.000000, 2.000000, 3.000000, 4.000000, 5.000000, 6.000000, 7.000000, 8.000000, 9.000000]
-/
#guard_msgs in
#eval evalGrad
         (fun x : Float^[10] =>
           IndexType.foldl (init:=(0:Float))
             (fun s i => s + 0.5 * (toVec x i)^2))
         (hf := by data_synth => conv => enter[3]; lsimp)
         (fromVec fun i => i.1.toFloat)



/--
info: [1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000, 1.000000]
-/
#guard_msgs in
#eval evalGrad
         (fun x : Float^[10] =>
           IndexType.foldl (init:=(0:Float))
             (fun s i => s + (toVec x i)))
         (hf := by data_synth => conv => enter[3]; lsimp)
         (fromVec fun i => i.1.toFloat)
