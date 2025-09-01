import SciLean.Analysis.Calculus.HasRevFDeriv

namespace SciLean

set_option linter.unusedVariables false

class HasRevFDerivMonad (K : Type) [RCLike K]
    (m : Type → Type) (m' : outParam $ Type → Type)
    [Monad m] [Monad m'] where

  HasRevFDerivM
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
    (f : X → m Y) (f' : X → m (Y × (Y → m' X))) : Prop

  HasRevFDerivM_pure
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
    (f : X → Y) {f'} (hf : HasRevFDeriv K f f') :
    HasRevFDerivM (fun x => pure (f x))
      (fun x =>
        let' (y,df) := f' x
        pure (y, fun dy => pure (df dy)))

  HasRevFDerivM_bind
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
    {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]
    (g : X → m Y) {g'} (hg : HasRevFDerivM g g')
    (f : Y → m Z) {f'} (hf : HasRevFDerivM f f') :
    HasRevFDerivM (fun x => g x >>= f)
      (fun x => do
        let ydg ← g' x
        -- let' (y,dg) := ydg  -- some problem with `let'` and do notation
        let zdf ← f' ydg.1
        let' (y,dg) := ydg
        let' (z,df) := zdf
        pure (z, fun dz => do
          let dy ← df dz
          let dx ← dg dy
          pure dx))

  HasRevFDerivM_pair
    {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
    {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
    (f : X → m Y) {f'} (hf : HasRevFDerivM f f') :
    HasRevFDerivM (fun x => do let y ← f x; pure (x,y))
      (fun x => do
        let ydf ← f' x
        let' (y,df) := ydf
        pure ((x,y), fun dxy : X×Y => do
          let dx ← df dxy.2
          pure (dxy.1 + dx)))


export HasRevFDerivMonad (HasRevFDerivM)


attribute [data_synth out f' in f] HasRevFDerivM

set_option deprecated.oldSectionVars true

variable
  (K : Type) [RCLike K]
  {m : Type → Type} {m' : outParam $ Type → Type}
  [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  [HasRevFDerivMonad K m m']
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]

open HasRevFDerivMonad

@[data_synth out f' in f]
structure HasRevFDerivUpdateM (f : X → m Y) (f' : X → m (Y × (Y → X → m' X))) : Prop where
  deriv :
    HasRevFDerivM K f
      (fun x => do
        let ydf ← f' x
        let' (y,df) := ydf
        pure (y, fun dy => do
          let dx ← df dy 0
          pure dx))
  eq : ∀ x dy dx,
    (do
      let dx := (← f' x).2 dy dx
      pure dx)
    =
    (do
      let dx' := (← f' x).2 dy 0
      pure (dx' >>= fun dx' => pure (dx + dx')))

variable {K}

----------------------------------------------------------------------------------------------------

-- id_rule does not make sense
-- const_rule has to be specific to every monad

@[fun_trans]
theorem HasRevFDerivM.comp_rule
    (g : X → Y) {g'} (hg : HasRevFDeriv K g g')
    (f : Y → m Z) {f'} (hf : HasRevFDerivM K f f') :
    HasRevFDerivM K
      (fun x => f (g x))
      (fun x => do
        let ydg := g' x
        let zdf ← f' ydg.1
        pure (zdf.1,
              fun dz => do
                let dy ← zdf.2 dz
                pure (ydg.2 dy))) := by
  have h := HasRevFDerivM_bind (m:=m) (m':=m')
    (fun x => pure (g x)) (HasRevFDerivM_pure g hg) f hf
  simp_all


@[fun_trans]
theorem HasRevFDerivUpdateM.comp_rule
    (g : X → Y) {g'} (hg : HasRevFDerivUpdate K g g')
    (f : Y → m Z) {f'} (hf : HasRevFDerivM K f f') :
    HasRevFDerivUpdateM K
      (fun x => f (g x))
      (fun x => do
        let ydg := g' x
        let zdf ← f' ydg.1
        pure (zdf.1,
              fun dz dx => do
                let dy ← zdf.2 dz
                pure (ydg.2 dy dx))) := by
  sorry_proof


@[fun_trans]
theorem HasRevFDerivM.let_rule
    (g : X → Y) {g'} (hg : HasRevFDerivUpdate K g g')
    (f : Y → X → m Z) {f'} (hf : HasRevFDerivM K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasRevFDerivM K (fun x => let y := g x; f y x)
      (fun x => do
        let ydg := g' x
        let zdf ← f' (ydg.1,x)
        pure (zdf.1,
              fun dz => do
                let dyx ← zdf.2 dz
                let dx := ydg.2 dyx.1 dyx.2
                pure dx)) := by
  have hg' : HasRevFDeriv K g (fun x => let ydg := g' x; (ydg.1, fun dy => ydg.2 dy 0)) := sorry_proof
  have h := HasRevFDerivM_bind (m:=m) (m':=m')
    (fun x => pure (g x, x)) (HasRevFDerivM_pure _ (by data_synth)) _ hf
  simp at h
  simp_all
  -- we just need `(g' x).2 a.1 0 + a.2 = (g' x).2 a.1 a.2` and we are done!
  sorry_proof


@[fun_trans]
theorem HasRevFDerivUpdateM.let_rule
    (g : X → Y) {g'} (hg : HasRevFDerivUpdate K g g')
    (f : Y → X → m Z) {f'} (hf : HasRevFDerivUpdateM K (fun yx : Y×X => f yx.1 yx.2) f') :
    HasRevFDerivUpdateM K (fun x => let y := g x; f y x)
      (fun x => do
        let ydg := g' x
        let zdf ← f' (ydg.1,x)
        pure (zdf.1,
              fun dz dx => do
                let dyx ← zdf.2 dz (0,dx)
                let dx := ydg.2 dyx.1 dyx.2
                pure dx)) := by
  sorry_proof


open Lean Meta HasRevFDerivM in
#eval show MetaM Unit from do
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivM,``HasRevFDerivM.comp_rule⟩, .com⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivM, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivM,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩

open Lean Meta HasRevFDerivUpdateM in
#eval show MetaM Unit from do
   -- Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdateM,``HasRevFDerivUpdateM.comp_rule⟩, .com⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdateM, ``comp_rule⟩, .comp
      (← getConstArgId ``comp_rule `g) (← getConstArgId ``comp_rule `f)
      (← getConstArgId ``comp_rule `hg) (← getConstArgId ``comp_rule `hf)⟩
   Tactic.DataSynth.addLambdaTheorem ⟨⟨``HasRevFDerivUpdateM,``let_rule⟩, .letE
      (← getConstArgId ``let_rule `g) (← getConstArgId ``let_rule `f)
      (← getConstArgId ``let_rule `hg) (← getConstArgId ``let_rule `hf)⟩


end SciLean


--------------------------------------------------------------------------------

section CoreFunctionProperties

open SciLean HasRevFDerivMonad


set_option deprecated.oldSectionVars true

variable
  (K : Type _) [RCLike K]
  {m m'} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  [HasRevFDerivMonad K m m']
  {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]


--------------------------------------------------------------------------------
-- Pure.pure -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[data_synth]
theorem Pure.pure.arg_a0.HasRevFDerivM_rule
    (a0 : X → Y) {a0'} (ha0 : HasRevFDeriv K a0 a0') :
    HasRevFDerivM K (fun x => pure (f:=m) (a0 x))
      (fun x => do
        let ydf := a0' x
        pure (ydf.1, fun dy => pure (ydf.2 dy))) :=
  HasRevFDerivM_pure _ ha0

set_option linter.unusedVariables false in
@[data_synth]
theorem Pure.pure.arg.HasRevFDerivUpdateM_rule
    (a0 : X → Y) {a0'} (ha0 : HasRevFDerivUpdate K a0 a0') :
    HasRevFDerivUpdateM K
      (fun x => pure (f:=m) (a0 x))
      (fun x => do
        let ydf := a0' x
        pure (ydf.1,
              fun dy dx => pure (ydf.2 dy dx))) := by
  sorry_proof


--------------------------------------------------------------------------------
-- Bind.bind -------------------------------------------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false in
@[data_synth]
theorem Bind.bind.arg_a0a1.HasRevFDerivM_rule
    (a0 : X → m Y) {a0'} (ha0 : HasRevFDerivM K a0 a0')
    (a1 : X → Y → m Z) {a1'} (ha1 : HasRevFDerivM K (fun xy : X×Y => a1 xy.1 xy.2) a1') :
    HasRevFDerivM K (fun x => Bind.bind (a0 x) (a1 x))
      (fun x => do
        let ydg ← a0' x
        let zdf ← a1' (x,ydg.1)
        pure (zdf.1,
              fun dz => do
                let dxy ← zdf.2 dz
                let dx ← ydg.2 dxy.2
                pure (dxy.1 + dx))) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem Bind.bind.arg_a0a1.HasRevFDerivUpdateM_rule
    (a0 : X → m Y) {a0'} (ha0 : HasRevFDerivUpdateM K a0 a0')
    (a1 : X → Y → m Z) {a1'} (ha1 : HasRevFDerivUpdateM K (fun xy : X×Y => a1 xy.1 xy.2) a1') :
    HasRevFDerivUpdateM K (fun x => Bind.bind (a0 x) (a1 x))
      (fun x => do
        let ydg ← a0' x
        let zdf ← a1' (x,ydg.1)
        pure (zdf.1,
              fun dz dx => do
                let dxy ← zdf.2 dz (dx,0)
                let dx ← ydg.2 dxy.2 dxy.1
                pure dx)) := by
  sorry_proof



-- Functor.map -----------------------------------------------------------------
--------------------------------------------------------------------------------

set_option linter.unusedVariables false in
@[data_synth]
theorem Functor.map.arg_a0a1.HasRevFDerivM_rule
  (a0 : X → Y → Z) {a0'} (ha0 : HasRevFDeriv K (fun xy : X×Y => a0 xy.1 xy.2) a0')
  (a1 : X → m Y) {a1'} (ha1 : HasRevFDerivUpdateM K a1 a1') :
  HasRevFDerivM K (fun x => (a0 x) <$> (a1 x))
    (fun x => do
      let ydy ← a1' x
      let y := ydy.1; let dy' := ydy.2
      let zdz := a0' (x,y)
      let z := zdz.1; let dz' := zdz.2
      return (z, fun dz => do
            let dxdy := dz' dz
            let dx := dxdy.1
            let dy := dxdy.2
            let dx ← dy' dy dx
            return dx)) := by
  sorry_proof

set_option linter.unusedVariables false in
@[data_synth]
theorem Functor.map.arg_a0a1.HasRevFDerivUpdateM_rule
  (a0 : X → Y → Z) {a0'} (ha0 : HasRevFDerivUpdate K (fun xy : X×Y => a0 xy.1 xy.2) a0')
  (a1 : X → m Y) {a1'} (ha1 : HasRevFDerivUpdateM K a1 a1') :
  HasRevFDerivUpdateM K (fun x => (a0 x) <$> (a1 x))
    (fun x => do
      let ydy ← a1' x
      let y := ydy.1; let dy' := ydy.2
      let zdz := a0' (x,y)
      let z := zdz.1; let dz' := zdz.2
      return (z, fun dz dx => do
            let dxdy := dz' dz (dx,0)
            let dx := dxdy.1
            let dy := dxdy.2
            let dx ← dy' dy dx
            return dx)) := by
  sorry_proof
