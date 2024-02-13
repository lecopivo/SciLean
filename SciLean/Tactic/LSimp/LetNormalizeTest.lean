import SciLean.Tactic.LSimp.LetNormalize
import SciLean.Util.RewriteBy
import SciLean.Util.Profile

open SciLean.Tactic

opaque id' {α} (a : α) : α := a

axiom hihi {α} (a : α) : id' a = a

-- #profile_this_file 1
set_option profiler true
set_option profiler.threshold 1

#check
    (let x3 :=
      let x2 :=
        let x1 := 10
        x1 + 5
      x2
    let h1 :=
      let h2 := id' 2
      h2 + 1
    let foo := fun x => let a := (10 + 15, 42 + 7); id' (a.1 + id' x + a.2)
    let y5 :=
      let y1 := 4
      let y2 := foo 5
      (let y3 := 14; let f1 := fun x => let fy1 := let fy2 := 4; fy2; let fy3 := x + x; x + 100 + fy1 + fy3; y1 + y3 + f1 h1) + (let y4 := 56; y2 + y4)
    let z3 :=
      (let z1 := 1; z1 + z1, let z2 := 2; z2 * z2)
    x3 + y5 + z3.1 + z3.2)
    rewrite_by
      simp (config:={singlePass:=true,zeta:=false,dsimp:=false}) only [↓let_normalize]




#check
    (fun (x y : Nat) =>
      let a := x + 1
      let b := x + a
      let c := x + y
      a+b+c)
    rewrite_by
      simp (config:={singlePass:=true,zeta:=false}) only [↓let_normalize]
