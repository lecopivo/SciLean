import SciLean

open SciLean


theorem mapMono_mapMono {I} [IndexType I] (x : Float^[I]) (f g : Float → Float) :
    (x.mapMono f |>.mapMono g) = x.mapMono fun x => f (g x) := sorry_proof

open Scalar
def softMax {I} [IndexType I]
  (r : Float) (x : Float^[I]) : Float^[I] := Id.run do
  let m := x.reduce (max · ·)
  let x := x.mapMono fun x => x-m
  let x := x.mapMono fun x => exp r*x
  let w := x.reduce (·+·)
  let x := x.mapMono fun x => x/w
  return x


def softMax_optimized {I} [IndexType I] (r : Float) (x : Float^[I]) :=
    (softMax r x)
    rewrite_by
      unfold softMax
      let_unfold x
      simp (config:={zeta:=false}) only [mapMono_mapMono]
