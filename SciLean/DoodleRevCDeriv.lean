import SciLean
import SciLean.Util.Profile
import SciLean.Tactic.LetNormalize
import SciLean.Util.RewriteBy

open SciLean

variable 
  {K : Type} [IsROrC K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {ι : Type} [Fintype ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


set_default_scalar K 

theorem cderiv.uncurry_rule (f : X → Y → Z)
  (hf : IsDifferentiable K (fun xy : X×Y => f xy.1 xy.2))
  : cderiv K (fun xy : X×Y => f xy.1 xy.2)
    =
    fun xy dxy =>
      cderiv K (fun x => f x xy.2) xy.1 dxy.1
      +
      cderiv K (fun y => f xy.1 y) xy.2 dxy.2 := sorry_proof

theorem revCDeriv.prod_rule
  (f : X → Y → X×Y → Z) (hf : HasAdjDiff K (fun x : X×Y×(X×Y) => f x.1 x.2.1 x.2.2))
  : revCDeriv K (fun xy : X × Y => f xy.1 xy.2 xy)
    =
    fun x =>
      let ydf := revCDeriv K (fun x : X×Y×(X×Y) => f x.1 x.2.1 x.2.2) (x.1,x.2,x)
      (ydf.1,
       fun dz => 
         let dxy := ydf.2 dz
         (dxy.1, dxy.2.1) + dxy.2.2) := 
by
  -- simp [cderiv.uncurry_rule _ hf]
  sorry_proof

open BigOperators
theorem revCDeriv.pi_rule_v1
  (f : (i : ι) → X → (ι → X) → Y) (hf : ∀ i, HasAdjDiff K (fun x : X×(ι→X) => f i x.1 x.2))
  : (revCDeriv K fun (x : ι → X) (i : ι) => f i (x i) x)
    =
    fun x =>
      let xdf₁ := fun i => ∇ x':=x i, f i x' x
      let xdf₂ := ∇ x':=x, fun i => f i (x i) x'
      (fun i => f i (x i) x, 
       fun dy i => xdf₁ i (dy i) + xdf₂ dy i) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  have : ∀ i x, IsDifferentiable K (fun x' => f i x' x) := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x' x) x'') := sorry_proof
  have : ∀ i x, IsDifferentiable K (fun x' => f i x x') := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x x') x'') := sorry_proof
  unfold gradient; unfold revCDeriv
  funext x; ftrans; ftrans; simp
  funext dy i; 
  ftrans; 
  conv in (cderiv _ _) => 
    rw[cderiv.uncurry_rule (K:=K) (f i) (by fprop)]
  simp;
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  rw[semiAdjoint.pi_rule _ _ sorry_proof]
  simp
  ftrans



theorem revCDeriv.pi_rule_v1'
  (f : (i : ι) → X → (ι → X) → Y) (hf : ∀ i, HasAdjDiff K (fun x : X×(ι→X) => f i x.1 x.2))
  : (revCDeriv K fun (x : ι → X) (i : ι) => f i (x i) x)
    =
    fun x =>
      let xdf := fun i => (<∂ x' : X×(ι→X), fun i' => f i' x'.1 x'.2) (x i, x)
      (fun i => (xdf i).1 i, 
       fun dy i => ((xdf i).2 dy).1 + ((xdf i).2 dy).2 i) :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  have : ∀ i x, IsDifferentiable K (fun x' => f i x' x) := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x' x) x'') := sorry_proof
  have : ∀ i x, IsDifferentiable K (fun x' => f i x x') := sorry_proof
  have : ∀ i x x'', HasSemiAdjoint K (cderiv K (fun x' => f i x x') x'') := sorry_proof
  unfold revCDeriv
  funext x; simp; funext dy i; ftrans; ftrans; simp
  conv in (cderiv _ _) => 
    rw[cderiv.uncurry_rule (K:=K) (f i) (by fprop)]
  conv =>
    rhs
    enter[1,1,2,i]
    simp[cderiv.uncurry_rule (K:=K) (f i) (by fprop)]
    ftrans
  sorry_proof



example 
  : revCDeriv K (fun xy : X×Y => (xy.1,xy.2))
    =
    fun xy => 
      (xy, fun dxy => dxy) := 
by
  conv => 
    lhs; autodiff; enter[x]; let_normalize


example 
  : revCDeriv K (fun xy : X×Y => (xy.2,xy.1))
    =
    fun xy => 
      ((xy.2,xy.1), fun dxy => (dxy.2, dxy.1)) := 
by
  conv => 
    lhs; autodiff; enter[x]; let_normalize

#eval 0

#check
   (∇ (x : Fin 10 → K), fun i => x i)
   rewrite_by
     unfold gradient
     rw[revCDeriv.pi_rule_v1 (K:=K) (fun i x _ => x) (by fprop)]
     symdiff
     -- rw[revCDeriv.pi_rule _ _ (by fprop)]
     -- ftrans
     -- simp

     -- ftrans
    

#exit 

example : ∀ (i : SciLean.Idx n), SciLean.HasAdjDiff Float (fun x : Float^Idx n => ‖x[i]‖₂²) := by fprop

set_option trace.Meta.Tactic.ftrans.step true in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.discharge true in
#check 
  ∇ (x : Idx n → Float), (fun i => x i)
  rewrite_by
    symdiff

set_option trace.Meta.Tactic.ftrans.step true in
set_option trace.Meta.Tactic.fprop.step true in
#check 
   (<∂ x : Idx n → Float, fun i => x i)
   rewrite_by
     rw [revCDeriv.pi_rule _ _ (by fprop)]
     ftrans; simp


set_option trace.Meta.Tactic.simp.rewrite true in
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.ftrans.step true in
#check 
  ∇ (x : Idx n → Float), ∑ i, x i
  rewrite_by
    symdiff

