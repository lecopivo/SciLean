noncomputable
instance (S : Type _) [Vec K S] : FwdDerivMonad K (StateM S) (StateM (S×S)) where
  fwdDerivM f := fun x dx sds => 
    -- ((y,s'),(dy,ds'))
    let r := fwdCDeriv K (fun (xs : _×S) => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
    -- ((y,dy),(s',ds'))
    ((r.1.1,r.2.1),(r.1.2, r.2.2))

  fwdDerivValM x := fun sds => 
    -- ((y,s'),(dy,ds'))
    let r := fwdCDeriv K x sds.1 sds.2
    -- ((y,dy),(s',ds'))
    ((r.1.1,r.2.1),(r.1.2, r.2.2))

  IsDifferentiableM f := IsDifferentiable K (fun (xs : _×S) => f xs.1 xs.2)
  IsDifferentiableValM x := IsDifferentiable K x

  fwdDerivM_pure f h := 
    by 
      simp[pure, StateT.pure, fwdCDeriv]
      funext x dx sds
      rw[Prod.mk.arg_fstsnd.cderiv_rule (K:=K) (fun xs : _×S => f xs.1) (by fprop) (fun xs : _×S => xs.2) (by fprop)]
      ftrans; ftrans
      
  fwdDerivM_bind f g hf hg :=
    by 
      funext x dx sds
      simp[fwdCDeriv, bind, StateT.bind, StateT.bind.match_1]
      ftrans

  fwdDerivM_const x hx :=
    by 
      funext sds
      simp[fwdCDeriv, bind, StateT.bind, StateT.bind.match_1]
      ftrans

  IsDifferentiableM_pure f :=
    by 
      simp; constructor
      case mp => 
        intros
        simp[pure, StateT.pure]
        apply IsDifferentiable.comp_rule K (fun xs : _×S => (f xs.1, xs.2)) (fun xs => xs) (by fprop) (by fprop)
      case mpr => 
        intros
        simp[pure, StateT.pure]
        let g := Prod.fst ∘ (fun (xs : _×S) => pure (f:=StateM S) (f xs.fst) xs.snd) ∘ (fun x => (x,0))
        have : IsDifferentiable K (Prod.fst ∘ (fun (xs : _×S) => pure (f:=StateM S) (f xs.fst) xs.snd) ∘ (fun x => (x,0))) := by fprop
        have hg : IsDifferentiable K g := by fprop
        rw[show f = g by rfl]
        apply hg

  IsDifferentiableM_IsDifferentiableValM y :=
    by 
      simp; constructor
      intros; fprop
      intro hy
      apply IsDifferentiable.comp_rule K (fun xs : _×S => y xs.2) (fun s : S => (0,s)) hy (by fprop)
