import SciLean

open SciLean

----------------------------------------------------------------------------------------------------

namespace Array
def fibonacci (n : Nat) : Array Nat := Id.run do
    let mut fib : Array Nat := Array.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1
    for i in [2:n] do
        fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib

/--
info: #[0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
-/
#guard_msgs in
#eval fibonacci 10

end Array


----------------------------------------------------------------------------------------------------

namespace DataArray

def fibonacci (n : Nat) : DataArray UInt64 := Id.run do
    let mut fib : DataArray UInt64 := DataArray.mkEmpty n
    fib := fib.push 0
    fib := fib.push 1

    for i in [2:n] do
      fib := fib.push (fib[i-1]! + fib[i-2]!)
    return fib

/--
info: ⊞[0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
-/
#guard_msgs in
#eval fibonacci 10

end DataArray


----------------------------------------------------------------------------------------------------

namespace List

def fibonacci (n : Nat) : List Nat :=
  (go n []).reverse
  where
    go (n : Nat) (l : List Nat) : List Nat :=
      match n, l with
      |   0,       l  => l
      | n+1,       [] => go n [0]
      | n+1,    x::[] => go n [1, x]
      | n+1, x::y::l  => go n ((x+y)::x::y::l)

/--
info: [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
-/
#guard_msgs in
#eval fibonacci 10

end List
