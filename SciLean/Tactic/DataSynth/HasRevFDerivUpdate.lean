import SciLean.Tactic.DataSynth.HasRevFDeriv
import SciLean.Analysis.SpecialFunctions.Inner
import SciLean.Analysis.SpecialFunctions.Norm2

set_option linter.unusedVariables false

namespace SciLean

variable {R : Type} [RCLike R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]
  {Z : Type} [NormedAddCommGroup Z] [AdjointSpace R Z] [CompleteSpace Z]
  {X₁ : Type} [NormedAddCommGroup X₁] [AdjointSpace R X₁] [CompleteSpace X₁]
  {X₂ : Type} [NormedAddCommGroup X₂] [AdjointSpace R X₂] [CompleteSpace X₂]
  {I : Type} [IndexType I]

variable (R)
@[data_synth out f' in f]
structure HasRevFDerivUpdate (f : X → Y) (f' : X → Y×(Y→X→X))  where
  val : ∀ x, f' x
             =
             let' (y,df) := revFDeriv R f x;
             (y, fun dy dx => dx + df dy)
  prop : Differentiable R f
variable {R}


omit [CompleteSpace X] [CompleteSpace Y] in
theorem HasRevFDeriv_from_HasRevFDerivUpdate (f : X → Y) {f' : X → Y×(Y→X→X)} :
    HasRevFDerivUpdate R f f'
    →
    HasRevFDeriv R f (fun x => let' (y,df) := f' x; (y, fun dy => (df dy 0))) := by
  intro hf; cases hf
  constructor
  · intros; simp_all; rfl
  · fun_prop


namespace HasRevFDerivUpdate

@[data_synth]
theorem id_rule : HasRevFDerivUpdate R (fun x : X => x) (fun x => (x, fun dx dx₀ => dx₀ + dx)) := by
  constructor
  · fun_trans
  · fun_prop


theorem const_rule (y : Y) :  HasRevFDerivUpdate R (fun x : X => y) (fun x => (y, fun _ dx => dx)) := by
  constructor
  · fun_trans
  · fun_prop


theorem pi_rule (f : X → I → Y) (f' : I → _)
    (hf : ∀ i, HasRevFDerivUpdate R (f · i) (f' i)) :
    HasRevFDerivUpdate R
      (fun (x : X) i => f x i)
      (fun x =>
        (f x,
         fun dy dx =>
           IndexType.foldl (init:=dx) (fun dx i => (f' i x).2 (dy i) dx))) := by
  have hf' := fun i => (hf i).1
  have := fun i => (hf i).2
  constructor
  · intro dx
    fun_trans[hf']
    funext dy dx
    rw[revFDeriv.pi_rule (hf:=by fun_prop)]
    simp
    sorry_proof
  · apply differentiable_pi''
    assumption


theorem comp_rule (g : X → Y) (f : Y → Z) {f' g'}
    (hg : HasRevFDerivUpdate R g g') (hf : HasRevFDerivUpdate R f f') :
    HasRevFDerivUpdate R
      (fun x : X => f (g x))
      (fun x =>
        let' (y,dg) := g' x
        let' (z,df) := f' y
        (z, fun dz dx =>
              let dy := df dz 0
              dg dy dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


theorem let_rule (g : X → Y) (f : Y → X → Z) {f' g'}
    (hg : HasRevFDerivUpdate R g g')
    (hf : HasRevFDerivUpdate R (fun yx : Y×X => f yx.1 yx.2) f')  :
    HasRevFDerivUpdate R
      (fun x : X => let y := g x; f y x)
      (fun x =>
        let' (y,dg) := g' x
        let' (z,df) := f' (y,x)
        (z, fun dz dx =>
          let' (dy,dx) := df dz (0,dx);
          dg dy dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all; ac_rfl
  · fun_prop


omit [CompleteSpace X] [CompleteSpace Y] in
theorem letNonComp_rule (f : α → X → Y) {f' : α → _} (a : α)
    (hf : ∀ a, HasRevFDerivUpdate R (f a) (f' a))  :
    HasRevFDerivUpdate R
      (fun x : X => let b := a; f b x)
      (fun x => let b := a; f' b x) := hf a


omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace X₁]
     [AdjointSpace R X₂] [CompleteSpace X₂] [NormedAddCommGroup X₂] in
theorem proj_rule (f : X → Y) {g'}
    (g : X₁ → Y) (p₁ : X → X₁) (p₂ : X → X₂) (q : X₁ → X₂ → X)
    (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R f (fun x =>
      let x₁ := p₁ x
      let' (y,dg) := g' x₁;
      (y, fun dy dx =>
        let dx₁ := p₁ dx
        let dx₂ := p₂ dx
        let dx₁ := dg dy dx₁
        q dx₁ dx₂)) := by sorry_proof


end HasRevFDerivUpdate


@[data_synth]
theorem Prod.mk.arg_a0a1.HasRevFDerivUpdate_rule
  (f : X → Y) (g : X → Z) (f' g')
  (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun x => (f x, g x))
    (fun x =>
      let' (y,df) := f' x
      let' (z,dg) := g' x
      ((y,z), fun dyz dx =>
        let' (dy,dz) := dyz
        let dx := df dy dx
        dg dz dx)) := by

  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all; ac_rfl
  · fun_prop

@[data_synth]
theorem Prod.fst.arg_self.HasRevFDerivUpdate_rule
  (f : X → Y×Z) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R
    (fun x => (f x).1)
    (fun x =>
      let' ((y,z),df) := f' x
      (y, fun dy dx => df (dy,0) dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop

@[data_synth]
theorem Prod.snd.arg_self.HasRevFDerivUpdate_rule
  (f : X → Y×Z) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R
    (fun x => (f x).2)
    (fun x =>
      let' ((y,z),df) := f' x
      (z, fun dz dx => df (0,dz) dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


@[data_synth]
theorem HAdd.hAdd.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x + g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y + z, fun dy dx =>
                  let dx := df dy dx
                  dg dy dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all; ac_rfl
  · fun_prop


@[data_synth]
theorem HSub.hSub.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x - g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y - z, fun dy dx =>
                  let dx := df dy dx
                  dg (-dy) dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only;
    simp_all[revFDeriv,neg_pull]
    funext dy dx
    abel
  · fun_prop


@[data_synth]
theorem Neg.neg.arg_a0.HasRevFDerivUpdate_rule
    (f : X → Y) (f')
    (hf : HasRevFDerivUpdate R f f') :
    HasRevFDerivUpdate R (fun x => -f x)
      (fun x =>
        let' (y,df) := f' x
        (-y, fun dy dx => df (-dy) dx)) := by
  cases hf;
  constructor
  · intro dx; fun_trans only;
    simp_all[revFDeriv,neg_pull]
  · fun_prop


open ComplexConjugate
@[data_synth]
theorem HMul.hMul.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → R) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x * g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y * z, fun dy dx =>
           let dy₁ := (conj z) • dy
           let dy₂ := (conj y) • dy
           let dx := df dy₁ dx
           let dx := dg dy₂ dx
           dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push]
    ac_rfl
  · fun_prop


@[data_synth]
theorem HSMul.hSMul.arg_a0a1.HasRevFDerivUpdate_rule
    (f : X → R) (g : X → Y) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
    HasRevFDerivUpdate R (fun x => f x • g x)
      (fun x =>
        let' (y,df) := f' x
        let' (z,dg) := g' x
        (y • z, fun dy dx =>
           let dy₁ := ⟪z, dy⟫[R]
           let dy₂ := (conj y) • dy
           let dx := df dy₁ dx
           let dx := dg dy₂ dx
           dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push]
    ac_rfl
  · fun_prop


@[data_synth]
theorem HDiv.hDiv.arg_a0.HasRevFDerivUpdate_rule
    (f : X → R) (c : R) (f')
    (hf : HasRevFDerivUpdate R f f') :
    HasRevFDerivUpdate R
     (fun x => f x / c)
     (fun x =>
       let' (y,df) := f' x
       (y / c,
         fun dr dx =>
           let s := (conj c)⁻¹
           let dx := df (s*dr) dx
           dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans; simp_all
    funext dy dx
    simp[revFDeriv,smul_push,neg_pull,sub_eq_add_neg]
    fun_trans
  · fun_prop


@[data_synth]
theorem HDiv.hDiv.arg_a0a1.HasRevFDerivUpdate_rule
    (f g : X → R) (f' g')
    (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') /- (hx : ∀ x, g x ≠ 0)-/ :
    HasRevFDerivUpdate R
     (fun x => f x / g x)
     (fun x =>
       let' (y,df) := f' x
       let' (z,dg) := g' x
       (y / z,
         fun dr dx =>
           let s := ((conj z)^2)⁻¹
           let dx := df (s*(conj z)*dr) dx
           let dx := dg (-s*(conj y)*dr) dx
           dx)) := by
  cases hf; cases hg
  have hx : ∀ x, g x ≠ 0 := sorry_proof
  constructor
  · intro dx; fun_trans (disch:=apply hx) only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push,neg_pull,sub_eq_add_neg]
    ac_rfl
  · sorry_proof
    --fun_prop (disch:=apply hx) -- missing theorem about division


@[data_synth]
theorem HDiv.hDiv.arg_a0.HasRevFDerivUpdate_rule'
    (c : R)  :
    HasRevFDerivUpdate R
     (fun x : R => x / c)
     (fun x =>
       (x / c,
         fun dr dx =>
           let s := (conj c)⁻¹
           let dx := dx + (s*dr)
           dx)) := by
  have : c ≠ 0 := sorry_proof
  have : conj c ≠ 0 := sorry_proof
  constructor
  · intro dx; fun_trans (disch:=assumption)
    funext dy dx
    simp[revFDeriv,smul_push,neg_pull,sub_eq_add_neg]
    field_simp
    ring
  · fun_prop


@[data_synth]
theorem HInv.hInv.arg_a0.HasRevFDerivUpdate_rule
  (f : X → R) (f')
  (hf : HasRevFDerivUpdate R f f') (hx : ∀ x, f x ≠ 0) :
  HasRevFDerivUpdate R (fun x => (f x)⁻¹)
    (fun x =>
      let' (y,df) := f' x
      (y⁻¹, fun dy dx =>
        let dx := df (-((conj y)^2)⁻¹*dy) dx
        dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans (disch:=apply hx) only; simp_all
    funext dy dx
    simp[revFDeriv,neg_pull,smul_push]
  · sorry_proof


@[data_synth]
theorem HPow.hPow.arg_a0.HasRevFDerivUpdate_rule
  (f : X → R) (n : ℕ) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R (fun x => f x ^ n)
    (fun x =>
      let' (y,df) := f' x
      (y ^ n, fun dy dx =>
        let dx := df (n * (conj y)^(n-1) • dy) dx
        dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp[revFDeriv,smul_push]; ac_rfl
  · fun_prop


@[data_synth]
theorem sum.arg_f.HasRevFDerivUpdate
  {I : Type} [IndexType I]
  (f : W → I → X) (f' : I → _) (hz : ∀ i, HasRevFDerivUpdate R (f · i) (f' i)) :
  HasRevFDerivUpdate R
    (fun w => ∑ i, f w i)
    (fun w =>
      ((∑ i, f w i), fun dx dw =>
        IndexType.foldl (init:=dw)
          (fun dw (i : I) =>
            let' (_x,df) := f' i w
            df dx dw))) := by
  have := fun i => (hz i).val
  have : ∀ (i : I), Differentiable R fun x => f x i := fun i => (hz i).prop
  constructor
  · intro w; fun_trans[adjointFDeriv]
    sorry_proof
  · fun_prop


omit [CompleteSpace W] [CompleteSpace X] in
@[data_synth]
theorem ite.arg_te.HasRevFDerivUpdate_rule (c : Prop) (dec : Decidable c)
  (f g : W → X) (f' g') (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun w => if c then f w else g w)
    (fun w => if c then f' w else g' w) := by
  have ⟨hf',_⟩ := hf
  have ⟨hg',_⟩ := hg
  constructor
  · intro w;
    split_ifs <;> fun_trans[hf',hg']
  · fun_prop

omit [CompleteSpace W] [CompleteSpace X] in
@[data_synth]
theorem dite.arg_te.HasRevFDerivUpdate_rule (c : Prop) (dec : Decidable c)
  (f : W → c → X) (f' : c → _) (g : W → ¬c → X) (g' : ¬c → _)
  (hf : ∀ hc, HasRevFDerivUpdate R (f · hc) (f' hc))
  (hg : ∀ hc, HasRevFDerivUpdate R (g · hc) (g' hc)) :
  HasRevFDerivUpdate R
    (fun w => if h : c then f w h else g w h)
    (fun w => if h : c then f' h w else g' h w) := by
  have hf' := fun hc => (hf hc).1
  have _ := fun hc => (hf hc).2
  have hg' := fun hc => (hg hc).1
  have _ := fun hc => (hg hc).2
  constructor
  · intro w;
    split_ifs <;> fun_trans[hf',hg']
  · split_ifs <;> simp_all

section OverReals

variable {R : Type} [RealScalar R]
  {W : Type} [NormedAddCommGroup W] [AdjointSpace R W] [CompleteSpace W]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]
  {Y : Type} [NormedAddCommGroup Y] [AdjointSpace R Y] [CompleteSpace Y]


@[data_synth]
theorem Inner.inner.arg_a0a1.HasRevFDerivUpdate_rule
  (f g : X → Y) (f' g')
  (hf : HasRevFDerivUpdate R f f') (hg : HasRevFDerivUpdate R g g') :
  HasRevFDerivUpdate R
    (fun x => ⟪f x, g x⟫[R])
    (fun x =>
      let' (y,df) := f' x
      let' (z,dg) := g' x
      (⟪y,z⟫[R], fun dr dx =>
        let dx := df (conj dr • z) dx
        let dx := dg (conj dr • y) dx
        dx)) := by
  cases hf; cases hg
  constructor
  · intro dx; fun_trans only; simp_all
    funext dy dx
    simp [revFDeriv,smul_push]; ac_rfl
  · fun_prop


@[data_synth]
theorem Norm2.norm2.arg_a0.HasRevFDerivUpdate_rule
  (f : X → Y) (f')
  (hf : HasRevFDerivUpdate R f f') :
  HasRevFDerivUpdate R
    (fun x => ‖f x‖₂²[R])
    (fun x =>
      let' (y,df) := f' x
      let z := ‖y‖₂²[R];
      (z, fun dr dx =>
        let dx := df ((2 * conj dr) • y) dx
        dx)) := by
  cases hf
  constructor
  · intro dx; fun_trans only; simp_all
  · fun_prop


end OverReals
