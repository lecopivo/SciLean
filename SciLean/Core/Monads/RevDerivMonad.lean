import SciLean.Core.FunctionTransformations.RevDeriv

namespace SciLean


set_option linter.unusedVariables false in
class RevDerivMonad (K : Type) [IsROrC K] (m : Type → Type) (m' : outParam $ Type → Type) [Monad m] [Monad m'] where
  revDerivM {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] : ∀ (f : X → m Y) (x : X), m (Y × (Y → m' X))

  HasAdjDiffM {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
    : ∀ (f : X → m Y), Prop

  revDerivM_pure {X Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] (f : X → Y) (hf : HasAdjDiff K f)
    : revDerivM (fun x => pure (f:=m) (f x)) = fun x => let ydf := revDeriv K f x; pure (ydf.1, fun dy => pure (ydf.2 dy))
  revDerivM_bind
    {X Y Z : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] [SemiInnerProductSpace K Z]
    (f : Y → m Z) (g : X → m Y) (hf : HasAdjDiffM f) (hg : HasAdjDiffM g)
     : revDerivM (fun x => g x >>= f)
       =
       fun x => do
         let ydg ← revDerivM g x
         let zdf ← revDerivM f ydg.1
         pure (zdf.1, fun dz => zdf.2 dz >>= ydg.2)
  revDerivM_pair {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] -- is this really necessary?
    (f : X → m Y) (hf : HasAdjDiffM f)
    : revDerivM (fun x => do let y ← f x; pure (x,y))
      =
      (fun x => do
        let ydf ← revDerivM f x
        pure ((x,ydf.1), fun dxy : X×Y => do let dx ← ydf.2 dxy.2; pure (dxy.1 + dx)))


  HasAdjDiffM_pure {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y]
    (f : X → Y) (hf : HasAdjDiff K f)
    : HasAdjDiffM (fun x : X => pure (f x))
  HasAdjDiffM_bind {X Y Z: Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] [SemiInnerProductSpace K Z]
    (f : Y → m Z) (g : X → m Y)
    (hf : HasAdjDiffM f) (hg : HasAdjDiffM g)
    : HasAdjDiffM (fun x => g x >>= f)
  HasAdjDiffM_pair {X : Type} {Y : Type} [SemiInnerProductSpace K X] [SemiInnerProductSpace K Y] -- is this really necessary?
    (f : X → m Y) (hf : HasAdjDiffM f)
    : HasAdjDiffM (fun x => do let y ← f x; pure (x,y))


export RevDerivMonad (revDerivM HasAdjDiffM)

attribute [fun_trans] revDerivM
attribute [fun_prop] HasAdjDiffM

variable
  (K : Type _) [IsROrC K]
  {m : Type → Type} {m' : outParam $ Type → Type} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]

open RevDerivMonad

def revDerivValM (x : m X) : m (X × (X → m' Unit)) := do
  revDerivM K (fun _ : Unit => x) ()

def HasAdjDiffValM (x : m X) : Prop :=
  HasAdjDiffM K (fun _ : Unit => x)


--------------------------------------------------------------------------------
-- HasAdjDiffM -----------------------------------------------------------
--------------------------------------------------------------------------------
namespace HasAdjDiffM

-- id_rule does not make sense

@[fun_prop]
theorem const_rule (y : m Y) (hy : HasAdjDiffValM K y)
  : HasAdjDiffM K (fun _ : X => y) :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  apply HasAdjDiffM_bind
  apply hy
  apply HasAdjDiffM_pure
  fun_prop

@[fun_prop]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K f) (hg : HasAdjDiff K g)
  : HasAdjDiffM K (fun x => f (g x)) :=
by
  rw[show ((fun x => f (g x))
           =
           fun x => pure (g x) >>= f) by simp]
  apply HasAdjDiffM_bind _ _ hf
  apply HasAdjDiffM_pure g hg

@[fun_prop]
theorem let_rule
  (f : X → Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K (fun xy : X×Y => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : HasAdjDiffM K (fun x => let y := g x; f x y) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x, g x))
  rw[show ((fun x => f x (g x))
           =
           fun x => pure (g' x) >>= f') by simp]
  apply HasAdjDiffM_bind _ _ hf
  apply HasAdjDiffM_pure g'
  fun_prop



end HasAdjDiffM

--------------------------------------------------------------------------------
-- revDerivM -------------------------------------------------------------------
--------------------------------------------------------------------------------
namespace revDerivM

-- id_rule does not make sense


@[fun_trans]
theorem const_rule (y : m Y) (hy : HasAdjDiffValM K y)
  : revDerivM K (fun _ : X => y)
    =
    (fun _ => do
      let ydy ← revDerivValM K y
      pure (ydy.1,
            fun dy' => do
              let _ ← ydy.2 dy'
              pure 0)) :=
by
  have h : (fun _ : X => y)
           =
           fun _ : X => pure () >>= fun _ => y := by simp
  rw[h]
  rw[revDerivM_bind]
  rw[revDerivM_pure]
  fun_trans
  simp [revDerivValM]
  fun_prop
  apply hy
  apply HasAdjDiffM_pure; fun_prop

@[fun_trans]
theorem comp_rule
  (f : Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K f) (hg : HasAdjDiff K g)
  : revDerivM K (fun x => f (g x))
    =
    (fun x => do
      let ydg := revDeriv K g x
      let zdf ← revDerivM K f ydg.1
      pure (zdf.1,
            fun dz => do
              let dy ← zdf.2 dz
              pure (ydg.2 dy))) :=
by
  conv =>
    lhs
    rw[show ((fun x => f (g x))
             =
             fun x => pure (g x) >>= f) by simp]
    rw[revDerivM_bind f (fun x => pure (g x))
         hf (HasAdjDiffM_pure _ hg)]
    simp[revDerivM_pure g hg]

@[fun_trans]
theorem let_rule
  (f : X → Y → m Z) (g : X → Y)
  (hf : HasAdjDiffM K (fun xy : X×Y => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revDerivM K (fun x => let y := g x; f x y)
    =
    (fun x => do
      let ydg := revDeriv K g x
      let zdf ← revDerivM K (fun xy : X×Y => f xy.1 xy.2) (x,ydg.1)
      pure (zdf.1,
            fun dz => do
              let dxy ← zdf.2 dz
              let dx := ydg.2 dxy.2
              pure (dxy.1 + dx))) :=
by
  let f' := (fun xy : X×Y => f xy.1 xy.2)
  let g' := (fun x => (x,g x))
  have hg' : HasAdjDiff K g' := by rw[show g' = (fun x => (x,g x)) by rfl]; fun_prop
  conv =>
    lhs
    rw[show ((fun x => f x (g x))
             =
             fun x => pure (g' x) >>= f') by simp]
    rw[revDerivM_bind f' (fun x => pure (g' x)) hf (HasAdjDiffM_pure g' hg')]
    simp[revDerivM_pure (K:=K) g' hg']
    fun_trans; simp

end revDerivM


end SciLean


--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean

variable
  (K : Type _) [IsROrC K]
  {m m'} [Monad m] [Monad m'] [RevDerivMonad K m m']
  [LawfulMonad m] [LawfulMonad m']
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {E : ι → Type} [∀ i, SemiInnerProductSpace K (E i)]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Pure.pure.arg_a0.HasAdjDiffM_rule
  (a0 : X → Y)
  (ha0 : HasAdjDiff K a0)
  : HasAdjDiffM K (fun x => Pure.pure (f:=m) (a0 x)) :=
by
  apply RevDerivMonad.HasAdjDiffM_pure a0 ha0


@[fun_trans]
theorem Pure.pure.arg_a0.revDerivM_rule
  (a0 : X → Y)
  (ha0 : HasAdjDiff K a0)
  : revDerivM K (fun x => pure (f:=m) (a0 x))
    =
    (fun x => do
      let ydf := revDeriv K a0 x
      pure (ydf.1, fun dy => pure (ydf.2 dy))):=
by
  apply RevDerivMonad.revDerivM_pure a0 ha0


@[simp, ftrans_simp]
theorem Pure.pure.HasAdjDiffValM_rule (x : X)
  : HasAdjDiffValM K (pure (f:=m) x) :=
by
  unfold HasAdjDiffValM
  apply RevDerivMonad.HasAdjDiffM_pure
  fun_prop


@[simp, ftrans_simp]
theorem Pure.pure.arg.revDerivValM_rule (x : X)
  : revDerivValM K (pure (f:=m) x)
    =
    pure (x,fun dy => pure 0) :=
by
  unfold revDerivValM; rw[RevDerivMonad.revDerivM_pure]; fun_trans; fun_prop


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem Bind.bind.arg_a0a1.HasAdjDiffM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : HasAdjDiffM K a0) (ha1 : HasAdjDiffM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : HasAdjDiffM K (fun x => Bind.bind (a0 x) (a1 x)) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : HasAdjDiffM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply RevDerivMonad.HasAdjDiffM_pair a0 ha0
  have hf : HasAdjDiffM K f := by fun_prop

  apply RevDerivMonad.HasAdjDiffM_bind _ _ hf hg



@[fun_trans]
theorem Bind.bind.arg_a0a1.revDerivM_rule
  (a0 : X → m Y) (a1 : X → Y → m Z)
  (ha0 : HasAdjDiffM K a0) (ha1 : HasAdjDiffM K (fun (xy : X×Y) => a1 xy.1 xy.2))
  : (revDerivM K (fun x => Bind.bind (a0 x) (a1 x)))
    =
    (fun x => do
      let ydg ← revDerivM K a0 x
      let zdf ← revDerivM K (fun (xy : X×Y) => a1 xy.1 xy.2) (x,ydg.1)
      pure (zdf.1,
            fun dz => do
              let dxy ← zdf.2 dz
              let dx ← ydg.2 dxy.2
              pure (dxy.1 + dx))) :=
by
  let g := fun x => do
    let y ← a0 x
    pure (x,y)
  let f := fun xy : X×Y => a1 xy.1 xy.2

  rw[show (fun x => Bind.bind (a0 x) (a1 x))
          =
          fun x => g x >>= f by simp[f,g]]

  have hg : HasAdjDiffM K (fun x => do let y ← a0 x; pure (x,y)) :=
    by apply RevDerivMonad.HasAdjDiffM_pair a0 ha0
  have hf : HasAdjDiffM K f := by fun_prop

  rw [RevDerivMonad.revDerivM_bind _ _ hf hg]
  simp [RevDerivMonad.revDerivM_pair a0 ha0]


--------------------------------------------------------------------------------
-- d/ite -----------------------------------------------------------------------
--------------------------------------------------------------------------------

@[fun_prop]
theorem ite.arg_te.HasAdjDiffM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  (ht : HasAdjDiffM K t) (he : HasAdjDiffM K e)
  : HasAdjDiffM K (fun x => ite c (t x) (e x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[fun_trans]
theorem ite.arg_te.revDerivM_rule
  (c : Prop) [dec : Decidable c] (t e : X → m Y)
  : revDerivM K (fun x => ite c (t x) (e x))
    =
    fun y =>
      ite c (revDerivM K t y) (revDerivM K e y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]


@[fun_prop]
theorem dite.arg_te.HasAdjDiffM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  (ht : ∀ h, HasAdjDiffM K (t h)) (he : ∀ h, HasAdjDiffM K (e h))
  : HasAdjDiffM K (fun x => dite c (fun h => t h x) (fun h => e h x)) :=
by
  induction dec
  case isTrue h  => simp[ht,h]
  case isFalse h => simp[he,h]


@[fun_trans]
theorem dite.arg_te.revDerivM_rule
  (c : Prop) [dec : Decidable c]
  (t : c → X → m Y) (e : ¬c → X → m Y)
  : revDerivM K (fun x => dite c (fun h => t h x) (fun h => e h x))
    =
    fun y =>
      dite c (fun h => revDerivM K (t h) y) (fun h => revDerivM K (e h) y) :=
by
  induction dec
  case isTrue h  => ext y; simp[h]
  case isFalse h => ext y; simp[h]
