import SciLean.Data.EnumType
import SciLean.Data.Index
import Aesop

open SciLean

instance : Coe USize Float := ⟨λ n => n.toUInt64.toFloat⟩

def triangularNumberViaFin (n : USize) : IO Float := pure $ Id.run do
  let mut sum : Float := 0
  for i in fullRange (Fin n.toNat) do
    for j in fullRange (Fin i.1) do
      sum := sum + Float.sin i.1.toFloat + Float.cos j.1.toFloat
  pure sum


def triangularNumberViaFinFold (n : USize) : IO USize := 
  EnumType.foldM (fullRange (Fin n.toNat)) (init := (0 : USize)) (λ sum' i => 
    EnumType.foldM (fullRange (Fin i.1)) (init := sum' ) (λ sum'' j => pure $ sum'' + 1))

def triangularNumberViaIdx (n : USize) : IO Float := pure $ Id.run do
  let mut sum : Float := 0
  for i in fullRange (Idx n) do
    for j in fullRange (Idx i.1) do
      sum := sum + Float.sin i.1 + Float.cos j.1
  pure sum

def triangularNumberViaIdxFoldM (n : USize) : IO Float := pure $ Id.run do
  EnumType.foldM (fullRange (Idx n)) (init := (0 : Float)) (λ sum' i => 
    EnumType.foldM (fullRange (Idx i.1)) (init := sum' ) (λ sum'' j => sum'' + Float.sin i.1 + Float.cos j.1))

def triangularNumberViaIdxFold (n : USize) : IO Float := pure $ 
  EnumType.Idx.fold (fullRange (Idx n)) (init := (0 : Float)) (λ sum' i => 
    EnumType.Idx.fold (fullRange (Idx i.1)) (init := sum' ) (λ sum'' j => sum'' + Float.sin i.1 + Float.cos j.1))

def triangularNumberViaIdxSum (n : USize) : IO Float := pure $ Id.run do
  pure $ ∑ i : Idx n, ∑ j : Idx i.1, (Float.sin i.1 + Float.cos j.1)

def triangularNumberViaFinSum (n : USize) : IO Float := pure $ Id.run do
  pure $ ∑ i : Fin n.toNat, ∑ j : Fin i.1, (Float.sin i.1.toFloat + Float.cos j.1.toFloat)


def triangularNumberNaive (n : USize) : Thunk (IO USize) := Thunk.mk λ _ => do
  let mut sum : USize := 0
  for i in [0:n.toNat] do
    for j in [0:i] do
      sum := sum + 1
  pure sum

partial def triangularNumberRecursiveMatch (n : USize) : Thunk (IO USize) := Thunk.mk λ _ => do
    pure $ loop (n.toNat-2) (n.toNat-2) 0
  where 
    loop (i j : Nat) (sum : USize) : USize :=
      match i, j with
      | 0, 0 => (sum+1)
      | i'+1, 0 => loop i' i' (sum+1)
      | _, j'+1 => loop i j' (sum+1)


partial def triangularNumberRecursiveIf (n : USize) : IO USize := do
    pure $ loop (n-2) (n-2) 0
  where 
    loop (i j : USize) (sum : USize) : USize :=
      if j != 0 then
        loop i (j-1) (sum+1)
      else if i != 0 then
        loop (i-1) (i-1) (sum+1)
      else
        sum + 1

def staticComp (n : USize) : USize := Id.run do
  let mut sum : USize := 0
  for i in fullRange (Idx n) do
    for _ in fullRange (Idx i.1) do
      sum := sum + 1
  pure sum


def testFun (f : USize → IO Float) (n : USize) (msg : String) : IO Unit := do
  let (m, t) ← IO.time (f n)
  IO.println s!"Computing for n := {n}, result := {m}, method := {msg}, time := {t.printAsMillis}"

open Index in
def parallelJoin {α ι} [Index ι] (m : USize) (f : ι → α) (op : α → α → α) (unit : α) : α := Id.run do
  let n := size ι
  if n == 0 then
    return unit
  let mut tasks : Array (Task α) := Array.mkEmpty m.toNat
  let m := max 1 (min m n) -- cap min/max of `m` 
  let stride : USize := (n+m-1)/m
  let mut start : Idx n := ⟨0,sorry⟩
  let mut stop  : Idx n := ⟨stride-1, sorry⟩
  for i in fullRange (Idx m) do
    let r : EnumType.Range ι := some (fromIdx start, fromIdx stop)
    let partialJoin : Unit → α := λ _ => Id.run do
      let mut a := unit
      for i in r do
        a := op a (f i)
      a
    tasks := tasks.push (Task.spawn partialJoin)
    start := ⟨min (start.1 + stride) (n-1), sorry⟩
    stop  := ⟨min (stop.1 + stride) (n-1), sorry⟩

  let mut a := unit
  for t in tasks do
    a := op a t.get
  a


#eval show IO Unit from do

  let a := #[1,2,3,4,5,6]
  let mut b := a

  IO.println s!"a addres: {ptrAddrUnsafe a}"
  IO.println s!"b addres: {ptrAddrUnsafe b}"
  
  b := (dbgTraceIfShared "of b" b).set! 0 42

  IO.println s!"b addres after set: {ptrAddrUnsafe b}"

  IO.println a
  IO.println b

@[inline] def parallelSum {X} [Zero X] [Add X] (m : USize) (f : Idx n → X) : X := Id.run do
  if n == 0 then
    return 0
  if m == 0 || m == 1 then
    return ∑ i, f i
  let mut tasks : Array (Task X) := Array.mkEmpty m.toNat
  let m := max 1 (min m n) -- cap min/max of `m` 
  let stride : USize := (n+m-1)/m
  let mut start : Idx n := ⟨0,sorry⟩ 
  let mut stop  : Idx n := ⟨stride-1, sorry⟩
  for i in fullRange (Idx m) do
    let r : EnumType.Range (Idx n) := some (start,stop)
    let partialSum : Unit → X := λ _ => Id.run do
      let mut sum : X := 0
      for i in r do
        sum := sum + f i
      sum
    tasks := tasks.push (Task.spawn partialSum)
    start := ⟨min (start.1 + stride) (n-1), sorry⟩
    stop  := ⟨min (stop.1 + stride) (n-1), sorry⟩

  let mut sum : X := 0
  for t in tasks do
    sum := sum + t.get
  sum

def triangularNumberViaIdxParallelSum (threads : USize) (n : USize) : IO Float := pure $ Id.run do
  pure $ Index.parallelSum threads λ i : Idx n => ∑ j : Idx n, (Float.sin i.1 + Float.cos j.1)

def triangularNumberViaIdxParallelJoin (threads : USize) (n : USize) : IO Float := pure $ Id.run do
  pure $ Index.parallelJoin threads (λ i : Idx n => ∑ j : Idx n, (Float.sin i.1 + Float.cos j.1)) (λ x y => x + y) 0

def main (args : List String) : IO Unit := do
  
  let n := (args.head!.toNat?.getD 1000).toUSize -- 300000000

  -- testFun triangularNumberViaIdx n "Idx for loop"
  -- testFun triangularNumberViaIdxFoldM n "Idx foldM"
  -- testFun triangularNumberViaIdxFold n "Idx fold"
  -- testFun triangularNumberViaIdxSum n "Idx sum"

  testFun (triangularNumberViaIdxParallelSum 12) n "Idx parallel sum[12]"
  testFun (triangularNumberViaIdxParallelJoin 12) n "Idx parallel join[12]"
  testFun (triangularNumberViaIdxParallelSum 1) n "Idx parallel sum[1]"

  -- testFun triangularNumberViaFinSum n "Fin sum"
  -- let (n3, time3) ← IO.time (pure $ staticComp n)
  -- IO.println s!"Computed {n}-th triangular number {n0} with naive for loop in: {time0.printAsMillis}"
  -- IO.println s!"Computed {n}-th triangular number {n0'} with recursion match in: {time0'.printAsMillis}"
  -- IO.println s!"Computed {n}-th triangular number {n0''} with recursion if in: {time0''.printAsMillis}"
  -- IO.println s!"Computed {n}-th triangular number {n1} with Fin for loop in: {time1.printAsMillis}"
  -- IO.println s!"Computed {n}-th triangular number {n3} with Fin foldM in: {time3.printAsMillis}"
