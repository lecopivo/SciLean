import SciLean.Tactic.LSimp2.Elab
import SciLean.Util.RewriteBy

open SciLean

-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.rewrite true in
-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.lsimp.post true in

opaque foo1 {α} (a : α) : α := a

@[simp]
theorem foo1_id {α} (a : α) : foo1 a = a := sorry

set_option trace.Meta.Tactic.simp.rewrite true in
#check 
  (let a := foo1 (fun x => x) 1
   let b := foo1 (fun x => x) (foo1 (foo1 a))
   b)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})
    lsimp (config := {zeta:=false, singlePass := true})


def ar : Array Nat := #[1,2,3,4,5]


#check 
  (
   let b := 10
   id b
  )
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})



#check 
  (let a := (hold 1 + 1, hold 10)
   let b := hold 2
   let c := 
     let d := a
     id (a.1 + b + d.1 + a.2)
   a.1 + b + c + a.2)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})


#check 
  (
    let a := 
      let i := (3, 4)
      let c := 
        let a := hold 1
        hold i.1
      c
    let w := a + a
    w)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})


#check 
  (
    let a := 
      let i : Fin 5 := ⟨3, by simp⟩
      let c := 
        let a := hold 1 
        id (ar[i])
      c
    let w := a + a
    w)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})


#check 
  (fun x : Nat => 
    let a := 
      let b := 
        let a := hold 10
        (a,hold 20)
      let i := (3, 4)
      let c := 
        let a := b.1 + 10
        id (1 + 2 + 3 + i.1)
      c
    let w := a + a
    w)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})

#check 
  (fun x : Nat => 
    let a := 
      let c := 
        let a := 10 + 10
        (1 + 2 + 3 + a)
      c 
    let w := a + a
    w)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})


#check 
  (fun x : Nat => 
    let a := 
      let b := 
        let a := hold 10
        ((a,hold 20), hold 30)
      let i : Fin 5 := ⟨3, by simp⟩
      let c := 
        let a := b.1.2 + 10
        id (0 + b.1.1 + 3 + 0 + a + i.1 + ar[i])
      0 + b.2 + c + id (4 + 0)
    let d :=  
      let e := 11
      let foo := (fun i : Nat => i * 2, fun i : Nat => i * 3)
      id (a + 4 + foo.2 (id (e + x)))
    let z := (let y := 42; a + y) + d
    let w := z + 0
    w)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})



def foo := 
  (fun x : Nat => 
    let a := 
      let b := 
        let a := 10
        (a,(20,30))
      -- let i : Fin 10 := ⟨5, by simp⟩
      let c := 
        let a := b.2.1 + 10
        id (0 + b.1 + 3 + 0 + a)
      0 + b.2.2 + c + id (4 + 0)
    let d :=  
      let e := 11
      id (a + 4 + id (e + x))
    let z := a + d
    let w := z + 0
    w)
  rewrite_by
    lsimp (config := {zeta:=false, singlePass := true})


set_option trace.Meta.Tactic.simp.rewrite true in
example 
  : (fun x y : Nat => 
    let a := 
      let b := 
        let a := 10
        (a,(20,30))
      -- let i : Fin 10 := ⟨5, by simp⟩
      let c := 
        let a := b.2.1 + 10
        id (0 + b.1 + 3 + 0 + a)
      0 + b.2.2 + c + id (4 + 0)
    let d :=  
      let e := 11
      id (a + 4 + id (e + x))
    let z := a + d
    let w := z + 0 + y
    w)
    =
    let a := 10;
    let b0 := a;
    let b1 := 20;
    let b2 := 30;
    let a := b1 + 10;
    let c := b0 + 3 + a;
    let a := b2 + c + 4;
    let e := 11;
    fun x =>
    let d := a + 4 + (e + x);
    let z := a + d;
    fun y =>
    let w := z + y;
    w :=
by
  conv => lhs; lsimp (config := {zeta := false, singlePass := true})

