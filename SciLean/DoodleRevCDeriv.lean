import SciLean
import SciLean.Util.Profile
import SciLean.Tactic.LetNormalize
import SciLean.Util.RewriteBy

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  {Y₁ : Type} [SemiInnerProductSpace K Y₁]
  {Y₂ : Type} [SemiInnerProductSpace K Y₂]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


set_default_scalar K 

variable (K)
theorem revCDeriv.pi_map_rule {ι} [EnumType ι]
  (f : Y → ι → Z) (g : X → ι → Y)
  (hf : ∀ i, HasAdjDiff K (f · i))
  (hg' : ∀ j, HasAdjDiff K (g · j))
  : (revCDeriv K fun x i => f (g x i) i)
    = 
    let df' := fun i => gradient K (fun y => f y i)
    fun x => 
      let ydg := revCDeriv K g x
      (fun i => f (ydg.1 i) i, 
       fun dz => 
         let dy := fun i => df' i (ydg.1 i) (dz i)
         ydg.2 dy) := 
by
  sorry

theorem revCDeriv.pi_prod_rule {ι} [EnumType ι]
  (g₁ : W → ι → Y₁) (g₂ : W → ι → Y₂)
  : (<∂ w, fun i => (g₁ w i, g₂ w i))
    =
    fun w => 
      let ydg₁ := <∂ g₁ w
      let ydg₂ := <∂ g₂ w
      (fun i => (ydg₁.1 i, ydg₂.1 i),
       fun dy => 
         ydg₁.2 (fun i => (dy i).1) + ydg₂.2 (fun i => (dy i).2)) := 
by
  sorry_proof


theorem GetElem.getElem.arg_xs.revCDeriv_pi_rule {IX I X} [ArrayType IX I X] [Index I] [SemiInnerProductSpace K X]
  (xs : W → IX) (hxs : HasAdjDiff K xs)
  : (<∂ w, fun i => (xs w)[i])
    =
    fun w => 
      let xdx := <∂ xs w
      (fun i => xdx.1[i], 
       fun dx => 
         let dx := introElem fun i => dx i
         xdx.2 dx) := 
by
  sorry_proof


theorem revCDeriv.pi_uncurry_rule {ι κ} [EnumType ι] [EnumType κ]
  (f : X → ι → κ → Y) (hf : ∀ i j, HasAdjDiff K (fun x => f x i j))
  : (<∂ x, fun i j => f x i j)
    =
    fun x =>
      let ydf := <∂ x':=x, fun ij : ι×κ => f x' ij.1 ij.2
      (fun i j => ydf.1 (i,j), 
       fun dy => ydf.2 (fun ij : ι×κ => dy ij.1 ij.2)) := 
by
  sorry



variable {K}

theorem revCDeriv.factor_through_app [Index I] [Nonempty I] [Index J]
  (f : I → Y → Z) (g : X → J → Y) (h : I → J)
  (hf : ∀ i, HasAdjDiff K (f i)) (hg : HasAdjDiff K g) 
  (hg' : ∀ j, HasAdjDiff K (g · j)) (hh : Function.Bijective h)
  : (revCDeriv K fun x i => f i ((g x) (h i)))
    = 
    let df' := fun i => gradient K (fun y => f i y)
    let ih := Function.invFun h
    fun x => 
      let jydg := revCDeriv K g x
      (fun i => f i (jydg.1 (h i)), 
       fun dz => 
         let rhs := fun j => df' (ih j) (jydg.1 j) (dz (ih j))
         jydg.2 rhs) := 
by
  conv => 
    lhs
    autodiff
    simp [revCDeriv]
  funext x
  simp[revCDeriv,gradient]
  funext dz
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  sorry_proof -- it should be possible to push the sum insidep and be done


theorem revCDeriv.factor_through_app' [Index I]
  (f : I → Y → Z) (g : X → I → Y)
  (hf : ∀ i, HasAdjDiff K (f i)) (hg : ∀ i, HasAdjDiff K (g · i)) 
  : (revCDeriv K fun x i => f i ((g x) i))
    = 
    let df' := fun i => gradient K (fun y => f i y)
    fun x => 
      let jydg := revCDeriv K g x
      (fun i => f i (jydg.1 i), 
       fun dz => 
         let rhs := fun i => df' i (jydg.1 i) (dz i)
         jydg.2 rhs) := 
by
  conv => 
    lhs
    autodiff
    simp [revCDeriv]
  funext x
  simp[revCDeriv,gradient]
  funext dz
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  sorry_proof -- it should be possible to push the sum insidep and be done


theorem revCDeriv.factor_through_app'' [Index I]
  (f : I → Y₁ → Y₂ → Z) (g₁ : X → I → Y₁) (g₂ : X → I → Y₂)
  -- (hf : ∀ i, HasAdjDiff K (f i)) (hg : ∀ i, HasAdjDiff K (g · i)) 
  : (revCDeriv K fun x i => f i (g₁ x i) (g₂ x i))
    = 
    let df₁ := fun i y₂ => gradient K (fun y₁ => f i y₁ y₂)
    let df₂ := fun i y₁ => gradient K (fun y₂ => f i y₁ y₂)
    fun x => 
      let ydg₁ := <∂ x':=x, g₁ x'
      let ydg₂ := <∂ x':=x, g₂ x'
      (fun i => f i (ydg₁.1 i) (ydg₂.1 i), 
       fun dz => 
         let dy₁ := fun i => df₁ i (ydg₂.1 i) (ydg₁.1 i) (dz i)
         let dy₂ := fun i => df₂ i (ydg₁.1 i) (ydg₂.1 i) (dz i)
         ydg₁.2 dy₁ + ydg₂.2 dy₂) := 
by
  sorry_proof -- it should be possible to push the sum insidep and be done


theorem revCDeriv.factor_through_getElem 
  {I J JY} [ArrayType JY J Y] [Index I] [Nonempty I] [Index J] 
  (f : I → Y → Z) (g : X → JY) (h : I → J)
  (hf : ∀ i, HasAdjDiff K (f i)) (hg : HasAdjDiff K g) (hg' : ∀ i, HasAdjDiff K (fun x => (g x)[i])) (hh : Function.Bijective h)
  : (revCDeriv K fun x i => f i ((g x)[h i]))
    = 
    let df' := fun i => gradient K (fun y => f i y)
    let ih := Function.invFun h
    fun x => 
      let jydg := revCDeriv K g x
      (fun i => f i (jydg.1[h i]), 
       fun dz => 
         let rhs := introElem (Cont:=JY) (fun j => df' (ih j) (jydg.1[j]) (dz (ih j)))
         jydg.2 rhs) := 
by
  conv => 
    lhs
    autodiff
    simp [revCDeriv]
  funext x
  simp[revCDeriv,gradient]
  funext dz
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  sorry_proof -- it should be possible to push the sum inside and be done



variable {ι κ : Type} [Index κ] [Index ι] [Nonempty ι] [Nonempty κ] [PlainDataType K]


theorem revCDeriv.pi_uncurry_rule (f : ι → κ → X → Y) (hf : ∀ i j, HasAdjDiff K (f i j))
  : (<∂ x, fun i j => f i j x)
    =
    fun x =>
      let ydf := <∂ x':=x, fun ij : ι×κ => f ij.1 ij.2 x'
      (fun i j => ydf.1 (i,j), 
       fun dy => ydf.2 (fun ij : ι×κ => dy ij.1 ij.2)) := 
by
  sorry

theorem revCDeriv.pi_introElem_rule (f : ι → κ → X → K) (hf : ∀ i j, HasAdjDiff K (f i j))
  : (<∂ x, fun i => ⊞ j => f i j x)
    =
    fun x =>
      let ydf := <∂ x':=x, fun i j => f i j x'
      (fun i => ⊞ j => ydf.1 i j, 
       fun dy => 
         ydf.2 (fun i j => (dy i)[j])) := sorry

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


example (x : W → K ^ ι) (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i])) (hx : HasAdjDiff K x)
  : <∂ (fun w i => (x w)[i])
    =
    fun w => 
      let xdx := <∂ (w':=w), x w'
      (fun i => xdx.1[i], fun dy => let dy' := ⊞ i => dy i; xdx.2 dy') :=
by 
  conv => 
    lhs
    simp (config := {zeta := false}) only [revCDeriv.factor_through_getElem (K:=K) (fun _ y => y) (fun w => x w) (fun i => i) sorry sorry sorry sorry]
    autodiff


example 
  : <∂ (fun (x : K ^ ι) i => x[i])
    =
    fun x => 
      (fun i => x[i], fun dy => ⊞ i => dy i) :=
by 
  conv => 
    lhs
    simp (config := {zeta := false}) only [revCDeriv.factor_through_getElem (K:=K) (fun _ y => y) (fun x : K ^ ι => x) (fun i => i) sorry sorry sorry sorry]
    autodiff


example 
  : <∂ (fun (x : K ^ ι) i => (2:K) * x[i])
    =
    fun x => 
      (fun i => (2:K) * x[i], fun dy => ⊞ i => (2:K) * dy i) :=
by 
  conv => 
    lhs
    simp (config := {zeta := false}) only [revCDeriv.factor_through_getElem (K:=K) (fun _ y => 2 * y) (fun x : K ^ ι => x) (fun i => i) sorry sorry sorry sorry]
    autodiff


--------------------------------------------------------------------------------
-- <∂ w, fun i => ∑ j, A i j * (x w)[j] ----------------------------------------
--------------------------------------------------------------------------------

example 
  (A : ι → κ → K) (x : W → κ →  K) (hx : HasAdjDiff K x)
  : <∂ (fun w i => ∑ j, A i j * (x w j))
    =
    fun w => 
      let xdx := <∂ x w
      (fun i => ∑ j, A i j * xdx.1 j, 
       fun dy => 
         let dx := fun j => ∑ i, A i j * dy i
         xdx.2 dx) := 
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    -- !!we do not want to apply `pi_uncurry_rule` here!!
    -- simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_app' (K:=K) (fun j y i => A i j * y) x sorry sorry]
    autodiff
    autodiff
    
example 
  (A : ι → κ → K) (x : W → K ^ κ) (hx : HasAdjDiff K x)
  : <∂ (fun w i => ∑ j, A i j * (x w)[j])
    =
    fun w => 
      let xdx := <∂ x w
      (fun i => ∑ j, A i j * xdx.1[j], 
       fun dy => 
         let dx := ⊞ j => ∑ i, A i j * dy i
         xdx.2 dx) := 
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y i => A i j * y) x (fun i => i) sorry sorry sorry sorry]
    autodiff
    let_normalize
    simp (config := {zeta:=false}) only

example 
  (A : ι → κ → K) (x : W → K ^ κ) (hx : HasAdjDiff K x)
  : (<∂ w, ⊞ i => ∑ j, A i j * (x w)[j])
    =
    fun w => 
      let xdx := <∂ x w
      (⊞ i => ∑ j, A i j * xdx.1[j], 
       fun dy => 
         let dx := ⊞ j => ∑ i, A i j * dy[i]
         xdx.2 dx) := 
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    -- we do not want to apply `pi_introElem_rule` and `pi_uncurry_rule` here !!!
    -- it leads to a bad code
    -- simp (config := {zeta:=false}) only [revCDeriv.pi_introElem_rule _ sorry]
    -- simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y => ⊞ i => A i j * y) x (fun i => i) sorry sorry sorry sorry]
    autodiff
    autodiff


--------------------------------------------------------------------------------
-- <∂ w, fun i => ∑ j, A w (i,j) * x j -----------------------------------------
--------------------------------------------------------------------------------

example (A : W → (ι×κ) → K) (x : κ → K) (hA : ∀ ij, HasAdjDiff K (A · ij))
  : (<∂ w, fun i => ∑ j, A w (i,j) * x j)
    =
    fun w => 
      let AdA := <∂ A w
      (fun i : ι => ∑ (j : κ), AdA.1 (i,j) * x j,
       fun dy => 
         let dA := fun ij => x ij.2 * dy ij.1
         AdA.2 dA) := 
by 
  conv => 
    lhs
    conv => 
      enter [w,2,w']
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only 
      [revCDeriv.factor_through_app (K:=K)
        (fun (ji : κ×ι) A => A * x ji.1) A (fun ji => (ji.2, ji.1)) sorry sorry sorry sorry]
    let_normalize
    autodiff
    unfold hold
    let_normalize
    simp (config := {zeta:=false}) only
      [show (Function.invFun fun ji : κ×ι => (ji.snd, ji.fst))
            =
            fun ij : ι×κ => (ij.2, ij.1) by sorry]


example (A : W → DataArrayN K (ι×κ)) (x : K ^ κ) (hA : HasAdjDiff K A)
  : (<∂ w, ⊞ i => ∑ j, (A w)[(i,j)] * x[j])
    =
    fun w => 
      let AdA := <∂ A w
      (⊞ i : ι => ∑ (j : κ), AdA.1[(i,j)] * x[j],
       fun dy => 
         let dA := ⊞ ij =>  x[ij.2] * dy[ij.1]
         AdA.2 dA) := 
by 
  conv => 
    lhs
    conv => 
      enter [A,2,A']
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.pi_introElem_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only 
      [revCDeriv.factor_through_getElem (K:=K)
        (fun (ji : κ×ι) A => A * x[ji.1]) A (fun ji => (ji.2, ji.1)) sorry sorry sorry sorry]
    let_normalize
    autodiff
    simp (config := {zeta:=false}) only
      [show (Function.invFun fun ji : κ×ι => (ji.snd, ji.fst))
            =
            fun ij : ι×κ => (ij.2, ij.1) by sorry]
  

  
--------------------------------------------------------------------------------
-- <∂ w, fun i => ∑ j, A w (i,j) * (x w) j -----------------------------------------
--------------------------------------------------------------------------------

example (A : W → (ι×κ) → K) (x : W → κ → K) 
  (hA : ∀ ij, HasAdjDiff K (A · ij)) (hx : ∀ j, HasAdjDiff K (x · j))
  : (<∂ w, fun i => ∑ j, A w (i,j) * (x w) j)
    =
    fun w => 
      let AdA := <∂ A w
      let xdx := <∂ x w
      (fun i => ∑ j, AdA.1 (i,j) * xdx.1 j, 
       fun dy => 
         let dA := fun ij : ι×κ => xdx.1 ij.2 * dy ij.1
         let dx := fun j : κ => ∑ i, AdA.1 (i,j) * dy i
         AdA.2 dA + xdx.2 dx) :=
by 
  conv => 
    lhs
    conv => 
      enter [w,2,w']
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_app'' (K:=K)
        (fun (j : κ) (A' : ι → K) x' i => (A' i) * x') (fun w j i => A w (i,j)) (fun w j => x w j)]
    simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_app (K:=K)
        (fun (ji : κ×ι) A' => A') A (fun ji => (ji.2, ji.1)) sorry sorry sorry sorry]

    let_normalize
    let_normalize
    simp (config := {zeta:=false}) only
    conv => 
      enter [w,ih,ydg₁,ydg₂]
      autodiff
    simp (config := {zeta:=false}) only
      [show (Function.invFun fun ji : κ×ι => (ji.snd, ji.fst))
            =
            fun ij : ι×κ => (ij.2, ij.1) by sorry]



example (A : W → DataArrayN K (ι×κ)) (x : W → K ^ κ) 
  -- (hA : ∀ ij, HasAdjDiff K (A · ij)) (hx : ∀ j, HasAdjDiff K (x · j))
  : (<∂ w, ⊞ i => ∑ j, (A w)[(i,j)] * (x w)[j])
    =
    fun w => 
      let AdA := <∂ A w
      let xdx := <∂ x w
      (⊞ i => ∑ j, AdA.1[(i,j)] * xdx.1[j], 
       fun dy => 
         let dA := ⊞ ij : ι×κ => xdx.1[ij.2] * dy[ij.1]
         let dx := ⊞ j : κ => ∑ i, AdA.1[(i,j)] * dy[i]
         AdA.2 dA + xdx.2 dx) :=
by 
  conv => 
    lhs
    conv => 
      enter [w,2,w']
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_app'' (K:=K)
        (fun (j : κ) (A' : ι → K) x' => ⊞ i => (A' i) * x') (fun w j i => (A w)[(i,j)]) (fun w j => (x w)[j])]
    simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_app (K:=K)
        (fun (ji : κ×ι) A' => A') (fun w ij => (A w)[ij]) (fun ji => (ji.2, ji.1)) sorry sorry sorry sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_getElem (K:=K)
        (fun i x' => x') x (fun i => i) sorry sorry sorry sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_getElem (K:=K)
        (fun ij A' => A') A (fun ij => ij) sorry sorry sorry sorry]

    let_normalize
    let_normalize
    autodiff
    simp (config := {zeta:=false}) only
      [show (Function.invFun fun ji : κ×ι => (ji.snd, ji.fst))
            =
            fun ij : ι×κ => (ij.2, ij.1) by sorry]
    let_normalize
    simp (config := {zeta:=false})
  
  


example (x y z : W → K ^ κ) 
  : (<∂ w, ∑ j, (x w)[j] * (y w)[j] * (z w)[j]) 
    =
    fun w => 
      let xdx := <∂ x w
      let ydy := <∂ y w
      let zdz := <∂ z w
      (∑ j, xdx.1[j] * ydy.1[j] * zdz.1[j], 
       fun dr => 
         let dx := ⊞ j : κ => ydy.1[j] * (zdz.1[j] * dr)
         let dy := ⊞ j : κ => xdx.1[j] * (zdz.1[j] * dr)
         let dz := ⊞ j : κ => xdx.1[j] * ydy.1[j] * dr
         xdx.2 dx + ydy.2 dy + zdz.2 dz) :=
by 
  conv => 
    lhs
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_app'' (K:=K)
        (fun (j : κ) xy' z' => xy' * z') (fun w j => (x w)[j] * (y w)[j]) (fun w j => (z w)[j])]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_app'' (K:=K)
        (fun (j : κ) x' y' => x' * y') (fun w j => (x w)[j]) (fun w j => (y w)[j])]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_getElem (K:=K)
        (fun i x' => x') x (fun i => i) sorry sorry sorry sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_getElem (K:=K)
        (fun i x' => x') y (fun i => i) sorry sorry sorry sorry]
    simp (config := {zeta:=false}) only
      [revCDeriv.factor_through_getElem (K:=K)
        (fun i x' => x') z (fun i => i) sorry sorry sorry sorry]
    autodiff
    let_normalize
    simp (config := {zeta:=false})



example (x y : W → K ^ κ) (hx : HasAdjDiff K x) (hy : HasAdjDiff K x)
  (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i])) (hy : ∀ i, HasAdjDiff K (fun w => (y w)[i]))
  : (<∂ w, fun j => (x w)[j] * (y w)[j])
    =
    fun w => 
      let xdx := <∂ x w
      let ydy := <∂ y w
      (fun j => xdx.1[j] * ydy.1[j], 
       fun dr => 
         let dx := ⊞ j => ydy.1[j] * dr j
         let dy := ⊞ j => xdx.1[j] * dr j
         xdx.2 dx + ydy.2 dy) :=
by 
  conv =>
    lhs
    autodiff
    autodiff
  sorry

#eval 0

open Lean Meta Qq



def splitLambdaToComp' (e : Expr) (mk := ``Prod.mk) (fst := ``Prod.fst) (snd := ``Prod.snd) : MetaM (Expr × Expr) := do
  match e with 
  | .lam name _ _ _ => 
    let e ← instantiateMVars e
    lambdaTelescope e λ xs b => do
    -- withLocalDecl name bi type fun x => do
      let x := xs[0]!
      let b := b.instantiate1 x
      let xId := x.fvarId!

      let ys := b.getAppArgs
      let mut f := b.getAppFn

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      let mut ys' : Array Expr := #[]
      let mut zs  : Array Expr := #[]

      for y in ys, i in [0:ys.size] do
        if y.containsFVar xId then
          let zId ← withLCtx lctx instances mkFreshFVarId
          lctx := lctx.mkLocalDecl zId (name.appendAfter (toString i)) (← inferType y)
          let z := Expr.fvar zId
          zs  := zs.push z
          ys' := ys'.push y
          f := f.app z
        else
          f := f.app y

      let y' ← mkProdElem ys' mk
      let g  ← mkLambdaFVars xs y'

      f ← withLCtx lctx instances (mkLambdaFVars (zs ++ xs[1:]) f)
      f ← mkUncurryFun zs.size f mk fst snd

      return (f, g)
    
  | _ => throwError "Error in `splitLambdaToComp`, not a lambda function!"


/-- Returns number of leading lambda binders of an expression 

Note: ignores meta data -/
def _root_.Lean.Expr.getLamBinderNum (e : Expr) : Nat :=
  go 0 e
where
  go (n : Nat) : Expr → Nat
  | .lam _ _ b _ => go (n+1) b
  | .mdata _ e => go n e
  | _ => n

/-- Get body of multiple bindings

Note: ignores meta data -/
def _root_.Lean.Expr.bindingBodyRec : Expr → Expr
| .lam _ _ b _ => b.bindingBodyRec
| .forallE _ _ b _ => b.bindingBodyRec
| .mdata _ e => e.bindingBodyRec
| e => e


#check Prod.mk
#check GetElem.getElem

def revCDeriv.modifiedFTransExt := {revCDeriv.ftransExt with 
  piRule := fun e F => do

    let n := F.getLamBinderNum
    IO.println n

    if n ≤ 1 then
      throwError "Not pi case"

    let body := F.bindingBodyRec

    if 2 < n then
      let .some K := e.getArg? 0 | return none
      let thrm ← mkAppM ``revCDeriv.pi_uncurry_rule #[K, F]
      SciLean.FTrans.tryTheorems
        #[{ proof := thrm, origin := .decl ``GetElem.getElem.arg_xs.revCDeriv_pi_rule, rfl := false}]
        revCDeriv.discharger e
    else 

    -- in case n == 2

    if body.isAppOf ``GetElem.getElem then
      IO.println s!"Is application of getElem!" 

      let f ← lambdaTelescope F fun xs b => 
        mkLambdaFVars #[xs[0]!] (b.getArg! 5)

      let .some K := e.getArg? 0 | return none
      let thrm ← mkAppM ``GetElem.getElem.arg_xs.revCDeriv_pi_rule #[K, f]
      SciLean.FTrans.tryTheorems
        #[{ proof := thrm, origin := .decl ``GetElem.getElem.arg_xs.revCDeriv_pi_rule, rfl := false}]
        revCDeriv.discharger e

    else if body.isAppOf ``Prod.mk then
      IO.println s!"Is application of Prod.mk!" 

      -- return none
      let (g₁,g₂) ← lambdaTelescope F fun xs b => do
        pure (← mkLambdaFVars xs (b.getArg! 2),
              ← mkLambdaFVars xs (b.getArg! 3))

      let .some K := e.getArg? 0 | return none
      let thrm ← mkAppM ``revCDeriv.pi_prod_rule #[K, g₁, g₂]
      SciLean.FTrans.tryTheorems
        #[ { proof := thrm, origin := .decl ``revCDeriv.pi_prod_rule, rfl := false} ]
        revCDeriv.discharger e

    else 
      try 
        let (f, g) ← splitLambdaToComp' F
        IO.println (← ppExpr f)
        IO.println (← ppExpr g)
        if (← isDefEq F f) then
          IO.println s!"split is trivial" 
        else
          IO.println s!"split is not trivial"

        IO.println s!"hohoo" 

        let .some K := e.getArg? 0 | return none
        let thrm ← mkAppM ``revCDeriv.pi_map_rule #[K, f, g]
        SciLean.FTrans.tryTheorems
          #[ { proof := thrm, origin := .decl ``revCDeriv.pi_map_rule, rfl := false} ]
          revCDeriv.discharger e

      catch _ => 
        IO.println s!"failed splitting"
        return none
    }
 
-- register revCDeriv
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revCDeriv, revCDeriv.modifiedFTransExt))

variable (A : W → DataArrayN K (ι×κ)) (hA : HasAdjDiff K A) (x y : W → K^κ) (hx : HasAdjDiff K x) (hy : HasAdjDiff K y) (h : κ → κ) (hh : Function.Bijective h)

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.rewrite true in
set_option pp.notation false
set_option pp.funBinderTypes true
example 
  : <∂ (fun w i => 2 * (x w)[i] * (y w)[i])
    =
    0 := 
by 
  conv =>
    lhs 
    ftrans only
    let_normalize
    autodiff
    let_normalize (config := {removeNoFVarLet := true})


  sorry_proof


#check 
  (<∂ w, fun i => (x w)[i])
  rewrite_by
    autodiff

example 
  : (<∂ w, fun j => (x w)[j])
    = 
    0 :=
by
  conv => 
    lhs
    autodiff
  sorry_proof

example
  : (<∂ w, fun i (_ : κ) => (x w)[i])
    =
    0 :=
by
  conv => 
    lhs
    autodiff
  sorry_proof

set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
example 
  : <∂ (fun w j i => (A w)[(i,j)])
    =
    0 := 
by 
  conv =>
    lhs
    ftrans only
    autodiff
  sorry_proof

set_option profiler true
set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
example 
  : <∂ (fun w j i => (A w)[(i,j)] * (x w)[j])
    =
    0 := 
by 
  conv =>
    lhs 
    ftrans only
    unfold gradient
    ftrans only
    let_normalize
    let_normalize
    simp (config := {zeta:=false})
  sorry_proof


#eval show MetaM Unit from do 
  withLocalDeclQ `x default q(Float → DataArrayN Float (Idx 10)) fun x => do
  let e := q(fun w i => ($x w)[i])
  let (f, g) ← splitLambdaToComp' e
  IO.println (← ppExpr f)
  IO.println (← ppExpr g)


#exit

  withLocalDeclQ `A default q(Float → Fin 10 → Fin 15 → Float) fun A => do
  withLocalDeclQ `x default q(Float → Fin 15 → Float) fun x => do

  let e := q(fun w i j => (($A w) i j, ($x w) j))
  let (f, g) ← splitLambdaToComp' e
  IO.println (← ppExpr f)
  IO.println (← ppExpr g)

  IO.println ""

  let e := q(fun w j i => ($A w) i j)
  let (f, g) ← splitLambdaToComp' e
  IO.println (← ppExpr f)
  IO.println (← ppExpr g)

  IO.println ""

  let e := q(fun w (_ : Fin 10) j => ($x w) j)
  let (f, g) ← splitLambdaToComp' e
  IO.println (← ppExpr f)
  IO.println (← ppExpr g)

  IO.println ""

  let e := q(fun w j => - ($x w) j)
  let (f, g) ← splitLambdaToComp' e
  IO.println (← ppExpr f)
  IO.println (← ppExpr g)
