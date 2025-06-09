import SciLean.Data.IndexType.Basic
import SciLean.Data.IndexType.Range

namespace SciLean


/-- Implementation of a fold over index type `I` in the monad `m`.

Note: This function is not part of `IndexType` because of the two universe parameters `v` and `w`
which were causing lot of issues during type class synthesis. -/
class FoldM (I : Type u) (m : Type v → Type w) where
  forIn {β} [Monad m] (r : IndexType.Range I) (init : β) (f : I → β → m (ForInStep β)) : m β

  -- TODO: some property that the forIn and foldM are doing the right thing in *the* order aligned
  --       with `IndexType`

/--
Abbreviation for `FoldM I Id`

Implementation of a fold over index type `I`.

Warning: This class has an universe parameter `v` that is not deducible from the its parameters.
  Sometimes you might have to specify the universe parameter manually e.g. `Fold.{_,0} I`
-/
abbrev Fold.{u,v} (I : Type u) := FoldM.{u,v,v} I Id

-- attribute [specialize, inline] FoldM.forIn

namespace IndexType

export FoldM (forIn)

@[inline, specialize, macro_inline]
def foldM {I n m β} [IndexType I n] [FoldM I m] [Monad m]
    (r : IndexType.Range I) (init : β) (f : I → β → m β) : m β :=
  forIn r init (fun i x => do return .yield (← f i x))

@[inline, specialize, macro_inline]
def fold {I n β} [IndexType I n] [FoldM I Id]
    (r : IndexType.Range I) (init : β) (f : I → β → β) : β :=
  foldM (m:=Id) r init (fun i x => pure (f i x))

instance {m : Type v → Type w} [FoldM I m] :
    ForIn m (IndexType.Range I) I where
  forIn := forIn

@[inline, macro_inline]
def reduceDM {I : Type u} {β : Type v} {m : Type v → Type w} {n : ℕ}
    [IndexType I n] [FoldM I m] [Monad m]
    (r : IndexType.Range I) (f : I → m β) (op : β → β → m β) (default : β) : m β := do
  let mut val := default
  let mut first : ULift.{v,0} Bool := ULift.up true
  for i in r do
    if ULift.down first then
      val ← f i
      first := ULift.up false
    else
      val ← op val (← f i)
  return val

@[inline, macro_inline]
def reduceD {I n β} [IndexType I n] [FoldM I Id]
    (r : IndexType.Range I) (f : I → β) (op : β → β → β) (default : β) : β :=
  reduceDM (m:=Id) r f op default

@[inline, macro_inline]
abbrev reduce {I n β} [IndexType I n] [FoldM I Id] [Inhabited β]
    (r : IndexType.Range I) (f : I → β) (op : β → β → β) : β :=
  reduceD r f op default


----------------------------------------------------------------------------------------------------
-- Instance for `Unit` -----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[inline]
instance : FoldM Unit m  where
  forIn r init f :=
    match r with
    | .empty => pure init
    | .full => do
       match ← f () init with
       | .done v | .yield v => pure v
    | .interval _ _ => do
       match ← f () init with
       | .done v | .yield v => pure v


----------------------------------------------------------------------------------------------------
-- Instance for `I × J` ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- TODO: This does not break correctly! Fix this!
--       It is not hard to implement but unclear if it negativelly impacts performance.
--       It will require careful testing.
@[inline]
instance
    {I nI} [IndexType I nI] [fi : FoldM I m]
    {J nJ} [IndexType J nJ] [fj : FoldM J m] :
    FoldM (I × J) m  where
  forIn r init f :=
    let (ri,rj) := r.ofProd
    fi.forIn ri init fun i x => do
      let x' ← fj.forIn rj x fun j x => f (i,j) x
      return .yield x'


----------------------------------------------------------------------------------------------------
-- Instance for `I ⊕ J` ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- TODO: this does not break correctly! fix this!
--       not hard to implement but unclear if it negativelly impacts performance
@[inline]
instance {I J n n'}
    [FirstLast I I] [IndexType I n] [FoldM I m]
    [FirstLast J J] [IndexType J n'] [FoldM J m] :
    FoldM (I ⊕ J) m  where
  forIn r init f :=
    match r.ofSum with
    | .inl (ri, rj) => do
      let x := init
      let x ← forIn ri x (fun i x => f (.inl i) x)
      let x ← forIn rj x (fun j x => f (.inr j) x)
      return x
    | .inr (rj, ri) => do
      let x := init
      let x ← forIn rj x (fun j x => f (.inr j) x)
      let x ← forIn ri x (fun i x => f (.inl i) x)
      return x


----------------------------------------------------------------------------------------------------
-- Instance for `Idx n` ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Run `f` for all `Idx n` -/
@[inline]
partial def Idx.forInFull {β} [Monad m]
    (init : β) (f : Idx n → β → m (ForInStep β)) : m β :=
  loop init 0
where
  @[specialize] loop (x : β) (i : USize) : m β := do
    if i < n.toUSize then
      match (← f ⟨i, sorry_proof⟩ x) with
      | .yield x => loop x (i+1)
      | .done x => pure x
    else
      pure x


/-- Run `f` starting at `a` up to `a`(inclusive) -/
@[inline]
partial def Idx.forInIntervalUp {β} [Monad m]
    (a b : Idx n) (init : β) (f : Idx n → β → m (ForInStep β)) : m β :=
  loop init a.1
where
  @[specialize] loop (x : β) (i : USize) : m β := do
    if i <= b.1 then
      match (← f ⟨i, sorry_proof⟩ x) with
      | .yield x => loop x (i+1)
      | .done x => pure x
    else
      pure x


/-- Run `f` starting at `b` down to `a`(inclusive) (assuming `a<b`)  -/
@[inline]
partial def Idx.forInIntervalDown {β} [Monad m]
    (a b : Idx n) (init : β) (f : Idx n → β → m (ForInStep β)) : m β :=
  loop init b
where
  @[specialize] loop (x : β) (i : Idx n) : m β := do
    match (← f i x) with
    | .yield x =>
      if a ≥ i then
        pure x
      else
        loop x ⟨i-1, sorry_proof⟩
    | .done x => pure x


@[inline]
instance : FoldM (Idx n) m  where
  forIn r init f :=
    match r with
    | .empty => pure init
    | .full => Idx.forInFull init f
    | .interval a b =>
      if a ≤ b then
        Idx.forInIntervalUp a b init f
      else
        Idx.forInIntervalDown b a init f


----------------------------------------------------------------------------------------------------
-- Instance for `Fin n` ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Run `f` for all `Fin n` -/
@[inline]
partial def Fin.forInFull {β} [Monad m]
    (init : β) (f : Fin n → β → m (ForInStep β)) : m β :=
  loopSmall init 0
where
  @[specialize] loopSmall (x : β) (i : USize) : m β := do
    if i < n.toUSize then
      match (← f ⟨i.toNat, sorry_proof⟩ x) with
      | .yield x => loopSmall x (i+1)
      | .done x => pure x
    else
      pure x


/-- Run `f` starting at `a` up to `a`(inclusive) -/
@[inline]
partial def Fin.forInIntervalUp {β} [Monad m]
    (a b : Fin n) (init : β) (f : Fin n → β → m (ForInStep β)) : m β :=
  loop init a.1.toUSize
where
  @[specialize] loop (x : β) (i : USize) : m β := do
    if i <= b.1.toUSize then
      match (← f ⟨i.toNat, sorry_proof⟩ x) with
      | .yield x => loop x (i+1)
      | .done x => pure x
    else
      pure x


/-- Run `f` starting at `b` down to `a`(inclusive) (assuming `a<b`)  -/
@[inline]
partial def Fin.forInIntervalDown {β} [Monad m]
    (a b : Fin n) (init : β) (f : Fin n → β → m (ForInStep β)) : m β :=
  loop init b
where
  @[specialize] loop (x : β) (i : Fin n) : m β := do
    match (← f i x) with
    | .yield x =>
      if a ≥ i then
        pure x
      else
        loop x ⟨i-1, sorry_proof⟩
    | .done x => pure x

@[inline]
instance : FoldM (Fin n) m  where
  forIn r init f :=
    match r with
    | .empty => pure init
    | .full => Fin.forInFull init f
    | .interval a b =>
      if a ≤ b then
        Fin.forInIntervalUp a b init f
      else
        Fin.forInIntervalDown b a init f


----------------------------------------------------------------------------------------------------
-- Instance for `Idx2 a b` ----------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Run `f` for all `Idx n` -/
@[inline]
partial def Idx2.forInFull {β} [Monad m]
    (init : β) (f : Idx2 a b → β → m (ForInStep β)) : m β :=
  loop init a.toInt64
where
  @[specialize] loop (x : β) (i : Int64) : m β := do
    if i ≤ b.toInt64 then
      match (← f ⟨i, sorry_proof⟩ x) with
      | .yield x => loop x (i+1)
      | .done x => pure x
    else
      pure x


/-- Run `f` starting at `a` up to `a`(inclusive) -/
@[inline]
partial def Idx2.forInIntervalUp {β} [Monad m]
    (a b : Idx2 c d) (init : β) (f : Idx2 c d → β → m (ForInStep β)) : m β :=
  loop init a.1
where
  @[specialize] loop (x : β) (i : Int64) : m β := do
    if i <= b.1 then
      match (← f ⟨i, sorry_proof⟩ x) with
      | .yield x => loop x (i+1)
      | .done x => pure x
    else
      pure x


/-- Run `f` starting at `b` down to `a`(inclusive) (assuming `a<b`)  -/
@[inline]
partial def Idx2.forInIntervalDown {β} [Monad m]
    (a b : Idx2 c d) (init : β) (f : Idx2 c d → β → m (ForInStep β)) : m β :=
  loop init b
where
  @[specialize] loop (x : β) (i : Int64) : m β := do
    match (← f ⟨i,sorry_proof⟩ x) with
    | .yield x =>
      if i ≤ a then
        pure x
      else
        loop x (i-1)
    | .done x => pure x


@[inline]
instance : FoldM (Idx2 a b) m  where
  forIn r init f :=
    match r with
    | .empty => pure init
    | .full => Idx2.forInFull init f
    | .interval a b =>
      if a ≤ b then
        Idx2.forInIntervalUp a b init f
      else
        Idx2.forInIntervalDown b a init f
