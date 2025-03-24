import SciLean.Data.IndexType.Fold


open SciLean


/--
info: 0 (0, 0)
0 (0, 1)
0 (1, 0)
0 (1, 1)
1 (0, 0)
1 (0, 1)
1 (1, 0)
1 (1, 1)
-/
#guard_msgs in
#eval show IO Unit from do
  let r := (IndexType.Range.full (I:=Idx 2))
  IndexType.foldM (m:=IO) (r.prod (r.prod r)) ()
    fun (i,j) _ => do
      IO.println s!"{i} {j}"

/--
info: 6 (0, 6)
6 (0, 5)
6 (0, 4)
6 (1, 6)
6 (1, 5)
6 (1, 4)
5 (0, 6)
5 (0, 5)
5 (0, 4)
5 (1, 6)
5 (1, 5)
5 (1, 4)
4 (0, 6)
4 (0, 5)
4 (0, 4)
4 (1, 6)
4 (1, 5)
4 (1, 4)
-/
#guard_msgs in
#eval show IO Unit from do
  let s := (IndexType.Range.full (I:=Idx 2))
  let r := (IndexType.Range.interval (I:=Idx 10) 6 4)
  IndexType.foldM (m:=IO) (r.prod (s.prod r)) ()
    fun (i,j) _ => do
      IO.println s!"{i} {j}"


/--
info: (inl 6)
(inl 7)
(inr 0)
(inr 1)
(inr 2)
(inr 3)
-/
#guard_msgs in
#eval show IO Unit from do
  let r := (IndexType.Range.interval (I:=Idx 8 ⊕ Idx 10) (.inl 6) (.inr 3))
  IndexType.foldM (m:=IO) r ()
    fun i _ => do
      IO.println s!"{i}"


/--
info: (inr 3)
(inr 2)
(inr 1)
(inr 0)
(inl 7)
(inl 6)
-/
#guard_msgs in
#eval show IO Unit from do
  let r := (IndexType.Range.interval (I:=Idx 8 ⊕ Idx 10) (.inr 3) (.inl 6))
  IndexType.foldM (m:=IO) r ()
    fun i _ => do
      IO.println s!"{i}"
