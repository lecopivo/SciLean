import SciLean.Data.IndexType

open SciLean



/--
info: (1, 4)
(1, 3)
(1, 2)
(2, 4)
(2, 3)
(2, 2)
-/
#guard_msgs in
#eval show IO Unit from do
  for i in intervalRange ((1,4) : Fin 5 × Fin 5) (2,2) do
    IO.println i


/--
info: (inl (1, 0))
(inl (1, 1))
(inl (1, 2))
(inl (2, 0))
(inl (2, 1))
(inl (2, 2))
(inr false)
-/
#guard_msgs in
#eval show IO Unit from do
  for i in intervalRange ((.inl (1,0)) : (Fin 3 × Fin 3) ⊕ Bool) (.inr false) do
    IO.println i



/--
info: (inl 1)
(inl 2)
(inl 3)
(inl 4)
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Fin 5 ⊕ Fin 5) (.interval (.inl 1) (.inl 4)) do
    IO.println i

/--
info: (inl 4)
(inl 3)
(inl 2)
(inl 1)
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Fin 5 ⊕ Fin 5) (.interval (.inl 4) (.inl 1)) do
    IO.println i


/--
info: (inr 1)
(inr 2)
(inr 3)
(inr 4)
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Fin 5 ⊕ Fin 10) (.interval (.inr 1) (.inr 4)) do
    IO.println i

/--
info: (inr 4)
(inr 3)
(inr 2)
(inr 1)
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Fin 5 ⊕ Fin 10) (.interval (.inr 4) (.inr 1)) do
    IO.println i


/--
info: (inl 3)
(inl 4)
(inr 0)
(inr 1)
(inr 2)
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Fin 5 ⊕ Fin 10) (.interval (.inl 3) (.inr 2)) do
    IO.println i


/--
info: (inr 2)
(inr 1)
(inr 0)
(inl 4)
(inl 3)
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Fin 5 ⊕ Fin 5) (.interval (.inr 2) (.inl 3)) do
    IO.println i



inductive Foo where
  | fst (i : Fin 2)
  | snd (i : Bool)
  | thrd (i : Fin 3)
deriving IndexType, Repr


/--
info: Foo.fst 1
Foo.snd false
Foo.snd true
Foo.thrd 0
Foo.thrd 1
Foo.thrd 2
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Foo) (.interval (.fst 1) (.thrd 2)) do
    IO.println (repr i)


/--
info: Foo.thrd 2
Foo.thrd 1
Foo.thrd 0
Foo.snd true
Foo.snd false
Foo.fst 1
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Foo) (.interval (.thrd 2) (.fst 1)) do
    IO.println (repr i)


/--
info: Foo.fst 0
Foo.fst 1
Foo.snd false
Foo.snd true
Foo.thrd 0
Foo.thrd 1
Foo.thrd 2
-/
#guard_msgs in
#eval! show IO Unit from do
  for i in IndexType.Iterator.start (I:=Foo) (.full) do
    IO.println (repr i)
