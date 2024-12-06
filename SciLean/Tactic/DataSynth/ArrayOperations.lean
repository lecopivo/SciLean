import SciLean.Data.DataArray
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate


namespace SciLean

set_option linter.unusedSectionVars false

variable
  {I : Type} [IndexType I]
  {J : Type} [IndexType J]
  {K : Type} [IndexType K]

variable [DecidableEq I] [DecidableEq J]

variable
  {R : Type} [inst : RealScalar R] [PlainDataType R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]


set_default_scalar R

namespace DataArrayN

@[data_synth]
theorem multiply.arg_xy.HasRevFDerivUpdate
  (x y : W → R^[I]) (x' y') (hx : HasRevFDerivUpdate R x x') (hy : HasRevFDerivUpdate R y y') :
  HasRevFDerivUpdate R
    (fun w => (x w).multiply (y w))
    (fun w =>
      let' (x,dx) := x' w;
      let' (y,dy) := y' w;
      (x.multiply y, fun dz dw =>
        let dzx := x.multiply dz
        let dzy := y.multiply dz
        let dw := dx dzy dw
        let dw := dy dzx dw
        dw)) := by
  cases hx; cases hy
  constructor
  · intro w; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem diag.arg_x.HasRevFDerivUpdate
  (x : W → R^[I]) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).diag)
    (fun w =>
      let' (x,dx) := x' w;
      (x.diag, fun dA dw =>
        let da := dA.diagonal
        dx da dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem diagonal.arg_x.HasRevFDerivUpdate
  (x : W → R^[I,I]) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).diagonal)
    (fun w =>
      let' (x,dx) := x' w;
      (x.diagonal, fun dA dw =>
        let da := dA.diag
        dx da dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem outerprod.arg_xy.HasRevFDerivUpdate
  (x : W → R^[I]) (y : W → R^[J]) (x' y') (hx : HasRevFDerivUpdate R x x') (hy : HasRevFDerivUpdate R y y') :
  HasRevFDerivUpdate R
    (fun w => (x w).outerprod (y w))
    (fun w =>
      let' (x,dx) := x' w;
      let' (y,dy) := y' w;
      (x.outerprod y, fun dA dw =>
        let dzx := dAᵀ * x
        let dzy := dA * y
        let dw := dx dzy dw
        let dw := dy dzx dw
        dw)) := by
  cases hx; cases hy
  constructor
  · intro w; fun_trans only; simp_all
    funext dA dw
    rw[add_assoc]; rfl
  · fun_prop


@[data_synth]
theorem sum.arg_x.HasRevFDerivUpdate
  (x : W → R^[I]) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).sum)
    (fun w =>
      let' (x,dx) := x' w;
      (x.sum, fun dr dw =>
        let da := dr • (1 : R^[I])
        dx da dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem transpose.arg_A.HasRevFDerivUpdate
  (A : W → R^[I,I]) (A') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w)ᵀ)
    (fun w =>
      let' (A,dA) := A' w;
      (Aᵀ, fun dB dw =>
        let dB' := dBᵀ
        dA dB' dw)) := by
  cases hA
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem lowerTriangular.arg_A.HasRevFDerivUpdate
  (x : W → R^[k]) (n : ℕ) (offset : ℕ := 0)
  (h : k = ((n-offset)*(n+1-offset))/2) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).lowerTriangular n offset h)
    (fun w =>
      let' (x,dx) := x' w;
      (x.lowerTriangular n offset h, fun dA dw =>
        let da := dA.lowerTriangularPart offset h
        dx da dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem lowerTriangularPart.arg_A.HasRevFDerivUpdate
  (A : W → R^[n,n]) (offset : ℕ := 0) {k}
  (h : k = ((n-offset)*(n+1-offset))/2) (A') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w).lowerTriangularPart offset h)
    (fun w =>
      let' (A,dA) := A' w;
      (A.lowerTriangularPart offset h, fun da dw =>
        let dB := da.lowerTriangular n offset h
        dA dB dw)) := by
  cases hA
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem trace.arg_A.HasRevFDerivUpdate
  (A : W → R^[I,I]) (A') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w).trace)
    (fun w =>
      let' (A,dA) := A' w;
      (A.trace, fun da dw =>
        let dB := (da • 𝐈)
        dA dB dw)) := by
  cases hA
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem dot.arg_xy.HasRevFDerivUpdate_rule
  (x y : W → R^[I]) (x' y') (hx : HasRevFDerivUpdate R x x') (hy : HasRevFDerivUpdate R y y') :
  HasRevFDerivUpdate R
    (fun w => (x w).dot (y w))
    (fun w =>
      let' (x,dx) := x' w;
      let' (y,dy) := y' w;
      (x.dot y, fun dz dw =>
        let dzx := dz • x
        let dzy := dz • y
        let dw := dx dzy dw
        let dw := dy dzx dw
        dw)) := by
  cases hx; cases hy
  constructor
  · intro w; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem vecmul.arg_xy.HasRevFDerivUpdate_rule
  (A : W → R^[I,J]) (x : W → R^[J]) (A' x')
  (hx : HasRevFDerivUpdate R x x') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w).vecmul (x w))
    (fun w =>
      let' (x,dx) := x' w;
      let' (A,dA) := A' w;
      (A.vecmul x, fun dz dw =>
        let dzx := dz.outerprod x
        let dzA := Aᵀ.vecmul dz
        let dw := dA dzx dw
        let dw := dx dzA dw
        dw)) := by
  cases hx; cases hA
  constructor
  · intro w; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem _root_.HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule
  (A : W → R^[I,J]) (x : W → R^[J]) (A' x')
  (hx : HasRevFDerivUpdate R x x') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w) * (x w))
    (fun w =>
      let' (x,dx) := x' w;
      let' (A,dA) := A' w;
      (A * x, fun dz dw =>
        let dzx := dz.outerprod x
        let dzA := Aᵀ * dz
        let dw := dA dzx dw
        let dw := dx dzA dw
        dw)) := by
  cases hx; cases hA
  constructor
  · intro w; fun_trans only; simp_all
    funext dz dw; rw[add_assoc]
  · fun_prop


@[data_synth]
theorem matmul.arg_xy.HasRevFDerivUpdate_rule
  (A : W → R^[I,J]) (B : W → R^[J,K]) (A' B')
  (hB : HasRevFDerivUpdate R B B') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w).matmul (B w))
    (fun w =>
      let' (A,dA) := A' w;
      let' (B,dB) := B' w;
      (A.matmul B, fun dz dw =>
        let dzB := dz.matmul Bᵀ
        let dzA := Aᵀ.matmul dz
        let dw := dA dzB dw
        let dw := dB dzA dw
        dw)) := by
  cases hA; cases hB
  constructor
  · intro w; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem _root_.HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule'
  (A : W → R^[I,J]) (B : W → R^[J,K]) (A' B')
  (hB : HasRevFDerivUpdate R B B') (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w) * (B w))
    (fun w =>
      let' (A,dA) := A' w;
      let' (B,dB) := B' w;
      (A * B, fun dz dw =>
        let dzB := dz * Bᵀ
        let dzA := Aᵀ * dz
        let dw := dA dzB dw
        let dw := dB dzA dw
        dw)) := by
  cases hA; cases hB
  constructor
  · intro w; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem inv.arg_A.HasRevFDerivUpdate
  (A : W → R^[I,I]) (A')
  (hA : HasRevFDerivUpdate R A A') (hA' : ∀ w, (A w).Invertible) :
  HasRevFDerivUpdate R
    (fun w => (A w).inv)
    (fun w =>
      let' (A,dA) := A' w;
      let iA := A.inv
      (iA, fun dy dw =>
        let dB := -iAᵀ * (dy * iAᵀ)
        dA dB dw)) := by
  cases hA
  constructor
  · intro w; fun_trans (disch:=apply hA') only; simp_all
  · fun_prop (disch:=apply hA')


@[data_synth]
theorem _root_.Inv.inv.arg_a0.HasRevFDerivUpdate_rule
  (A : W → R^[I,I]) (A')
  (hA : HasRevFDerivUpdate R A A') (hA' : ∀ w, (A w).Invertible) :
  HasRevFDerivUpdate R
    (fun w => (A w)⁻¹)
    (fun w =>
      let' (A,dA) := A' w;
      let iA := A⁻¹
      (iA, fun dy dw =>
        let dB := -iAᵀ * (dy * iAᵀ)
        dA dB dw)) := by
  cases hA
  constructor
  · intro w; fun_trans (disch:=apply hA') only; simp_all
  · fun_prop (disch:=apply hA')


@[data_synth]
theorem det.arg_A.HasRevFDerivUpdate
  (A : W → R^[I,I]) (A')
  (hA : HasRevFDerivUpdate R A A') :
  HasRevFDerivUpdate R
    (fun w => (A w).det)
    (fun w =>
      let' (A,dA) := A' w;
      let a := A.det
      (a, fun da dw =>
        let da := (a * da) • A⁻ᵀ
        dA da dw)) := by
  cases hA
  constructor
  · intro w; fun_trans (disch:=apply hA') only; simp_all
  · fun_prop


@[data_synth]
theorem solve.arg_Ab.HasRevFDerivUpdate_rule
  (A : W → R^[I,I]) (b : W → R^[I]) (A' b')
  (hA : HasRevFDerivUpdate R A A') (hA' : ∀ w, (A w).Invertible)
  (hb : HasRevFDerivUpdate R b b') :
  HasRevFDerivUpdate R
    (fun w => (A w).solve (b w))
    (fun w =>
      let' (A,dA) := A' w;
      let' (b,db) := b' w;
      let x := A.solve b
      (x, fun dz dw =>
        let dz := Aᵀ.solve dz
        let dzx := -dz.outerprod x
        let dw := dA dzx dw
        let dw := db dz dw
        dw)) := by
  cases hA; cases hb
  constructor
  · intro w; fun_trans (disch:=apply hA') only;
    simp_all only [revFDeriv.revFDeriv_fst, Prod.mk.injEq, true_and]
    simp only [revFDeriv, ↓adjoint.arg_y.neg_pull]; ac_rfl
  · fun_prop (disch := apply hA')



@[data_synth]
theorem solve'.arg_Ab.HasRevFDerivUpdate_rule
  (A : W → R^[I,I]) (B : W → R^[I,J]) (A' B')
  (hA : HasRevFDerivUpdate R A A') (hA' : ∀ w, (A w).Invertible)
  (hB : HasRevFDerivUpdate R B B') :
  HasRevFDerivUpdate R
    (fun w => (A w).solve' (B w))
    (fun w =>
      let' (A,dA) := A' w;
      let' (B,dB) := B' w;
      let X := A.solve' B
      (X, fun dZ dw =>
        let dZ := Aᵀ.solve' dZ
        let dzx := -(dZ * Xᵀ)
        let dw := dA dzx dw
        let dw := dB dZ dw
        dw)) := by
  cases hA; cases hB
  constructor
  · intro w; fun_trans (disch:=apply hA') only;
    simp_all only [revFDeriv.revFDeriv_fst, Prod.mk.injEq, true_and]
    simp only [revFDeriv, ↓adjoint.arg_y.neg_pull]; ac_rfl
  · fun_prop (disch := apply hA')





@[data_synth]
theorem softmax.arg_x.HasRevFDerivUpdate
  (x : W → R^[I]) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).softmax)
    (fun w =>
      let' (x,dx) := x' w;
      let xs := x.softmax
      (xs, fun dy dw =>
        let da := xs.multiply dy
        let db := ⟪xs,dy⟫ • xs
        let dy := da - db
        dx dy dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem logsumexp.arg_x.HasRevFDerivUpdate
  (x : W → R^[I]) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).logsumexp)
    (fun w =>
      let' (x,dx) := x' w;
      let s := x.logsumexp
      (s, fun dy dw =>
        let xs := x.softmax
        let dy := dy • xs
        dx dy dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem exp.arg_x.HasRevFDerivUpdate
  (x : W → R^[I]) (x') (hx : HasRevFDerivUpdate R x x') :
  HasRevFDerivUpdate R
    (fun w => (x w).exp)
    (fun w =>
      let' (x,dx) := x' w;
      let e := x.exp
      (e, fun dy dw =>
        let dy := e.multiply dy
        dx dy dw)) := by
  cases hx
  constructor
  · intro w; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem ArrayType.get.arg_cont.HasRevFDerivUpdate (i : I) :
  (HasRevFDerivUpdate R
    (fun x : R^[I] => x[i])
    (fun x => (x[i], fun dxi dx => ArrayType.modify dx i (fun xi => xi + dxi)))) := by

  constructor
  · intro w; fun_trans;
    funext dxi dx
    apply ArrayType.ext; intro j
    by_cases h : i = j <;> simp[h,oneHot]
  · fun_prop


@[data_synth]
theorem ArrayType.set.arg_contxi.HasRevFDerivUpdate (i : I)
  (x : W → R^[I]) (xi : W → R) (x' xi')
  (hx : HasRevFDerivUpdate R x x') (hxi : HasRevFDerivUpdate R xi xi') :
  (HasRevFDerivUpdate R
    (fun w => ArrayType.set (x w) i (xi w))
    (fun w =>
      let' (x,dx) := x' w;
      let' (xi,dxi) := xi' w;
      (ArrayType.set x i xi,
       fun dy dw =>
         let dw := dx (ArrayType.set dy i 0) dw
         let dw := dxi (dy[i]) dw
         dw))) := by
  cases hx; cases hxi
  constructor
  · intro w; fun_trans[revFDeriv]; simp_all; ac_rfl
  · fun_prop


-- @[data_synth]
-- theorem ArrayType.modify.arg_contxi.HasRevFDerivUpdate (i : I)
--   (x : W → R^[I]) (f : W → R → R) (x' f')
--   (hx : HasRevFDerivUpdate R x x') (hxi : HasRevFDerivUpdate R (fun x : W×R => f x.1 x.2) f') :
--   (HasRevFDerivUpdate R
--     (fun w => ArrayType.modify (x w) i (f w))
--     (fun w =>
--       let' (x,dx) := x' w;
--       let xi := x[i]
--       let' (xi,df) := f' (w,xi);
--       (ArrayType.set x i xi,
--        fun dy dw => sorry))) := sorry


@[data_synth]
theorem ArrayType.ofFn.arg_f.HasRevFDerivUpdate
  (f : W → I → R) (f' : I → _) (hz : ∀ i, HasRevFDerivUpdate R (f · i) (f' i)) :
  (HasRevFDerivUpdate R
    (fun w => ⊞ i => f w i)
    (fun w =>
       (⊞ i => f w i,
        fun dx dw =>
          IndexType.foldl (init:=dw) (fun dw (i : I) =>
            let' (y,df) := f' i w;
            df (dx[i]) dw)))) := by
  have := fun i => (hz i).val
  have : ∀ (i : I), Differentiable R fun x => f x i := fun i => (hz i).prop
  constructor
  · intro w; fun_trans;
    funext dx dw
    rw[revFDeriv.pi_rule (hf:=by fun_prop)]
    simp_all
    sorry_proof
  · fun_prop



example (f : W → I → X)
 (hf : ∀ (i : I), Differentiable R fun x => f x i)
  : Differentiable R fun w =>  ∑ i, f w i := by fun_prop

example : Differentiable R (fun x : R => ∑ (i : I), x) := by fun_prop

set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R^[I] => ∑ i, x[i]) _)
  rewrite_by
    data_synth

#check (HasRevFDerivUpdate R (fun x : R^[I] => ∑ i, x[i]*x[i]) _)
  rewrite_by
    data_synth

#check (HasRevFDerivUpdate R (fun x : R^[I] => ∑ i, x[i]*x[i]) _)
  rewrite_by
    data_synth

#check (HasRevFDerivUpdate R (fun x : R^[I] => ∑ i, let xi:= x[i]; (xi*xi + xi)) _)
  rewrite_by
    data_synth
    lsimp

set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R^[I] => (∑ i, x[i])•x) _)
  rewrite_by
    data_synth
    lsimp



set_option trace.Meta.Tactic.data_synth.input true in
set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R^[I] => (∑ i, x[i])*‖x - ‖x‖₂²•1‖₂²) _)
  rewrite_by
    data_synth
    lsimp



set_option trace.Meta.Tactic.data_synth true in
#check (HasRevFDerivUpdate R (fun x : R^[I] => (∑ i, x[i])*‖x - ‖x‖₂²•1‖₂²) _)
  rewrite_by
    data_synth
    lsimp
