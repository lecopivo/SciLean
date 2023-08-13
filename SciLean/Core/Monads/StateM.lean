import SciLean.Core.Monads.Id

namespace SciLean

variable {K : Type _} [IsROrC K]

noncomputable
instance (S : Type _) [Vec K S] : FwdDerivMonad K (StateM S) (StateM (S×S)) where
  fwdDerivM f := fun x dx sds => 
    -- ((y,s'),(dy,ds'))
    let r := fwdCDeriv K (fun (xs : _×S) => f xs.1 xs.2) (x,sds.1) (dx,sds.2)
    -- ((y,dy),(s',ds'))
    ((r.1.1,r.2.1),(r.1.2, r.2.2))

  IsDifferentiableM f := IsDifferentiable K (fun (xs : _×S) => f xs.1 xs.2)

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

  fwdDerivM_pair f hf := 
    by
      funext x dx sds
      simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      rw[Prod.mk.arg_fstsnd.fwdCDeriv_rule (K:=K) (fun xs : _×S => (xs.1, (f xs.1 xs.2).1)) (by fprop) (fun xs => (f xs.1 xs.2).2) (by fprop)]
      ftrans

  IsDifferentiableM_pure f :=
    by 
      simp;
      intros
      simp[pure, StateT.pure]
      apply Prod.mk.arg_fstsnd.IsDifferentiable_rule K (fun xs => xs.2) (fun xs : _×S => f xs.1) (by fprop) (by fprop)

  IsDifferentiableM_bind f g hf hg := 
    by
      simp; simp at hf; simp at hg
      simp[bind, StateT.bind, StateT.bind.match_1]
      fprop

  IsDifferentiableM_pair f hf := 
    by
      simp; simp at hf
      simp[bind, StateT.bind, StateT.bind.match_1, pure, StateT.pure]
      apply Prod.mk.arg_fstsnd.IsDifferentiable_rule K (fun xs => (f xs.1 xs.2).2) (fun xs : _×S => (xs.1, (f xs.1 xs.2).1))  (by fprop) (by fprop)


#eval 0







