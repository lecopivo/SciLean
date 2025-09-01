import SciLean

-- there are some linker issues :(

open SciLean


variable (R : Type) [RealScalar R]

set_default_scalar R


/--
info: fun x dx =>
  let x₁ := x * x;
  let x₂ := x * dx + x * dx;
  let x₁_1 := x₁ ^ 3;
  let x₂ := 3 • (x₁ ^ 2 * x₂);
  let x₁ := x₁_1 + x₁_1;
  let x₂ := x₂ + x₂;
  (x₁, x₂) : R → R → R × R
-/
#guard_msgs in
#check (∂> (x : R), Id'.run do
         let mut x := x
         x := x*x
         x := x^3
         x := x+x
         return x) rewrite_by autodiff

instance [NormedAddCommGroup X] : NormedAddCommGroup (ForInStep X) := sorry
instance {𝕜} [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X] : AdjointSpace 𝕜 (ForInStep X) := sorry

@[data_synth]
theorem asdf
  {𝕜} [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X] :
  HasRevFDeriv 𝕜 (fun x : X => ForInStep.yield x) (fun x => (.yield x, fun x' => x'.value)) := sorry_proof

@[data_synth]
theorem asdf''
  {𝕜} [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X] :
  HasRevFDerivUpdate 𝕜 (fun x : X => ForInStep.yield x) (fun x => (.yield x, fun x' x => x + x'.value)) := sorry_proof

@[fun_prop]
theorem asdf'
  {𝕜} [RCLike 𝕜] [NormedAddCommGroup X] [AdjointSpace 𝕜 X] :
  IsContinuousLinearMap 𝕜 (fun x : X => ForInStep.yield x) := sorry_proof


-- @[data_synth]
theorem forIn.hasRevFDerivM_rule_pure {I : Type} {nI} [IndexType I nI] (r : IndexType.Range I)
   (K : Type) [RCLike K]
   {m : Type → Type} {m' : outParam $ Type → Type}
   [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
   [HasRevFDerivMonad K m m']
   [FoldM I m]
   {W : Type} [NormedAddCommGroup W] [AdjointSpace K W]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   (f : W → I → X → m (ForInStep X)) {f' : I → _} (hf : ∀ i, HasRevFDerivM K (fun wx : W×X => f wx.1 i wx.2) (f' i))
   (x₀ : W → X) {x₀'} (hx₀ : HasRevFDeriv K x₀ x₀') :
   HasRevFDerivM K (fun w => forIn r (x₀ w) (fun i x => f w i x))
     (fun w => do
       let (x₀,dx₀) := x₀' w
       let mut x := x₀
       let mut df' : X → m' (W×X) := fun x => pure (0,x)
       for i in r do
         let (x', df) ← f' i (w,x)
         x := x'.value
         df' := fun dx => do
           let (dw,dx) ← df (.yield dx)
           let (dw',dx) ← df' dx
           pure (dw+dw', dx)
       pure (x, fun dx => do
         let (dw,dx) ← df' dx
         let dw' := dx₀ dx
         pure (dw + dw'))) := sorry_proof


@[data_synth]
theorem forIn.hasRevFDerivM_rule_pure' {I : Type} {nI} [IndexType I nI] (r : IndexType.Range I)
   (K : Type) [RCLike K]
   {m : Type → Type} {m' : outParam $ Type → Type}
   [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
   [HasRevFDerivMonad K m m']
   [FoldM I m]
   {W : Type} [NormedAddCommGroup W] [AdjointSpace K W]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   (f : W → I → X → m (ForInStep X)) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdateM K (fun wx : W×X => f wx.1 i wx.2) (f' i))
   (x₀ : W → X) {x₀'} (hx₀ : HasRevFDeriv K x₀ x₀') :
   HasRevFDerivM K (fun w => forIn r (x₀ w) (fun i x => f w i x))
     (fun w => do
       let (x₀,dx₀) := x₀' w
       let mut x := x₀
       let mut df' : X → W → m' (W×X) := fun x w' => pure (w',x)
       for i in r do
         let (x', df) ← f' i (w,x)
         x := x'.value
         df' := fun dx dw' => do
           let (dw,dx) ← df (.yield dx) (dw',0)
           let (dw,dx) ← df' dx dw
           pure (dw, dx)
       pure (x, fun dx => do
         let (dw,dx) ← df' dx 0
         let dw' := dx₀ dx
         pure (dw + dw'))) := sorry_proof


@[data_synth]
theorem forIn.hasRevFDerivUpdateM_rule_pure' {I : Type} {nI} [IndexType I nI] (r : IndexType.Range I)
   (K : Type) [RCLike K]
   {m : Type → Type} {m' : outParam $ Type → Type}
   [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
   [HasRevFDerivMonad K m m']
   [FoldM I m]
   {W : Type} [NormedAddCommGroup W] [AdjointSpace K W]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   (f : W → I → X → m (ForInStep X)) {f' : I → _} (hf : ∀ i, HasRevFDerivUpdateM K (fun wx : W×X => f wx.1 i wx.2) (f' i))
   (x₀ : W → X) {x₀'} (hx₀ : HasRevFDerivUpdate K x₀ x₀') :
   HasRevFDerivUpdateM K (fun w => forIn r (x₀ w) (fun i x => f w i x))
     (fun w => do
       let (x₀,dx₀) := x₀' w
       let mut x := x₀
       let mut df' : X → W → m' (W×X) := fun x w' => pure (w',x)
       for i in r do
         let (x', df) ← f' i (w,x)
         x := x'.value
         df' := fun dx dw' => do
           let (dw,dx) ← df (.yield dx) (dw',0)
           let (dw,dx) ← df' dx dw
           pure (dw, dx)
       pure (x, fun dx dw => do
         let (dw,dx) ← df' dx dw
         let dw := dx₀ dx dw
         pure dw)) := sorry_proof


instance
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X]
   {Y : Type} [NormedAddCommGroup Y] :
   NormedAddCommGroup (MProd X Y) := NormedAddCommGroup.ofEquiv' (proxy_equiv% (MProd X Y))

instance
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] :
   AdjointSpace K (MProd X Y) := AdjointSpace.ofEquiv' (proxy_equiv% (MProd X Y))

@[data_synth]
theorem MProd.fst.HasRevFDeriv_rule
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] :
   HasRevFDeriv K (fun xy : MProd X Y => xy.1) (fun xy => ⟨xy.1, fun dx => ⟨dx,0⟩⟩) := sorry_proof

@[data_synth]
theorem MProd.fst.HasRevFDerivUpdate_rule
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] :
   HasRevFDerivUpdate K (fun xy : MProd X Y => xy.1) (fun xy => ⟨xy.1, fun dx dxy => ⟨dxy.1 + dx, dxy.2⟩⟩) := sorry_proof

@[data_synth]
theorem MProd.snd.HasRevFDeriv_rule
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] :
   HasRevFDeriv K (fun xy : MProd X Y => xy.2) (fun xy => ⟨xy.2, fun dy => ⟨0,dy⟩⟩) := sorry_proof

@[data_synth]
theorem MProd.snd.HasRevFDerivUpdate_rule
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y] :
   HasRevFDerivUpdate K (fun xy : MProd X Y => xy.2) (fun xy => ⟨xy.2, fun dy dxy => ⟨dxy.1,dxy.2 + dy⟩⟩) := sorry_proof


@[data_synth]
theorem MProd.mk.HasRevFDeriv_rule
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
   {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]
   (f : X → Y) (g : X → Z) {f' g'} (hf : HasRevFDeriv K f f') (hg : HasRevFDerivUpdate K g g') :
   HasRevFDeriv K
     (fun x => MProd.mk (f x) (g x))
     (fun x =>
       let' (y,df') := f' x
       let' (z,dg') := g' x
       (⟨y,z⟩, fun dyz => dg' dyz.2 (df' dyz.1))) := sorry_proof

@[data_synth]
theorem MProd.mk.HasRevFDerivUpdate_rule
   {K : Type} [RCLike K]
   {X : Type} [NormedAddCommGroup X] [AdjointSpace K X]
   {Y : Type} [NormedAddCommGroup Y] [AdjointSpace K Y]
   {Z : Type} [NormedAddCommGroup Z] [AdjointSpace K Z]
   (f : X → Y) (g : X → Z) {f' g'} (hf : HasRevFDerivUpdate K f f') (hg : HasRevFDerivUpdate K g g') :
   HasRevFDerivUpdate K
     (fun x => MProd.mk (f x) (g x))
     (fun x =>
       let' (y,df') := f' x
       let' (z,dg') := g' x
       (⟨y,z⟩, fun dyz dx => dg' dyz.2 (df' dyz.1 dx))) := sorry_proof

set_option pp.proofs false

-- #check show (HasRevFDeriv R (fun (x : R) => Id'.run do
--          let mut x := x
--          for i in [:10] do
--            x += x^i.1.toNat
--          return x) _) from by
--   apply Id'.run.arg_x.HasRevFDeriv_rule
--   case hf =>
--     lsimp
--     data_synth => enter[3]; lsimp


-- #check show (HasRevFDeriv Float (fun (x : Float^[10]) => Id'.run do
--          let mut s : Float := 0
--          let mut p : Float := 1
--          for i in [:10] do
--            s += x[i]^2
--            p *= x[i]
--          return (s,p)) _) from by
--   apply Id'.run.arg_x.HasRevFDeriv_rule
--   case hf =>
--     lsimp
--     data_synth => enter[3]; lsimp

attribute [simp_core]
  bind_pure_comp
  bind_pure
  bind_map_left
  map_bind
  map_pure
  Functor.map_map
  ForInStep.value_yield
  Nat.succ_eq_add_one


/--
info: ⊞[2.000000, 4.000000, 6.000000, 8.000000, 10.000000, 12.000000, 14.000000, 16.000000, 18.000000, 20.000000]
-/
#guard_msgs in
#eval ((revFDeriv Float (fun (x : Float^[10]) => Id'.run do
         let mut s : Float := 0
         for i in [:10] do
           s += x[i]^2
         return s) ⊞[1.0,2,3,4,5,6,7,8,9,10]).2 1)
  rewrite_by
    autodiff


/--
info: ⊞[3628800.000000, 1814400.000000, 1209600.000000, 907200.000000, 725760.000000, 604800.000000, 518400.000000, 453600.000000, 403200.000000, 362880.000000]
-/
#guard_msgs in
#eval ((revFDeriv Float (fun (x : Float^[10]) => Id'.run do
         let mut p : Float := 1
         for i in [:10] do
           p *= x[i]
         return p) ⊞[1.0,2,3,4,5,6,7,8,9,10]).2 1)
  rewrite_by
    autodiff


/--
info: ⊞[3628800.000000, 1814400.000000, 1209600.000000, 907200.000000, 725760.000000, 604800.000000, 518400.000000, 453600.000000, 403200.000000, 362880.000000]
-/
#guard_msgs in
#eval ((revFDeriv Float (fun (x : Float^[10]) => Id'.run do
         let mut s : Float := 0
         let mut p : Float := 1
         for i in [:10] do
           s += x[i]^2
           p *= x[i]
         return (s,p)) ⊞[1.0,2,3,4,5,6,7,8,9,10]).2 (0,1))
  rewrite_by
    autodiff
