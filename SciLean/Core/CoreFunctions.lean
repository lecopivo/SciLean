import SciLean.Core.FunctionProperties


namespace SciLean

--------------------------------------------------------------------------------
-- Core bootstrapping theorems
--------------------------------------------------------------------------------

instance IsLin_is_IsSmooth {X Y : Type} {Xs Y' : Type} [Vec Xs] [Vec Y'] 
  (n : Nat) (f : X → Y) [Prod.Uncurry n (X → Y) Xs Y'] [inst : IsLinN n f] 
  : IsSmoothN n f := IsSmoothN.mk (toIsSmoothNT:=⟨inst.proof.2⟩)

@[diff] 
theorem diff_of_linear {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f]
  : ∂ f = λ _ dx => f dx := sorry_proof

@[diff] 
theorem diff_of_linear_2 {X Y Z} [Vec X] [Vec Y] [Vec Z] (f : X → Y → Z) [IsLinN 2 f]
  : ∂ (uncurryN 2 f) = λ _ (dx,dy) => f dx dy := sorry_proof


--------------------------------------------------------------------------------
-- Prod.fst - (·.1)
--------------------------------------------------------------------------------

function_properties Prod.fst {X Y} [Vec X] [Vec Y] (xy : X×Y) : X
argument xy
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := dxy.1 by symdiff -- ,
  -- abbrev 𝒯 := (xy.1, dxy.1) by symdiff

function_properties Prod.fst {X Y} [SemiHilbert X] [SemiHilbert Y] (xy : X×Y) : X
argument xy
  hasAdjoint := sorry_proof,
  abbrev † := ⟨xy',0⟩ by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; infer_instance,
  abbrev ∂† ℛ := (dxy', 0) by unfold adjointDifferential; symdiff; symdiff
  -- abbrev ℛ := (xy.1, λ dxy' => (dxy',0)) by symdiff


--------------------------------------------------------------------------------
-- Prod.snd - (·.2)
--------------------------------------------------------------------------------

function_properties Prod.snd {X Y} [Vec X] [Vec Y] (xy : X×Y) : Y
argument xy
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := dxy.2 by symdiff -- ,
  -- abbrev 𝒯 := (xy.2, dxy.2) by symdiff

function_properties Prod.snd {X Y} [SemiHilbert X] [SemiHilbert Y] (xy : X×Y) : Y
argument xy
  hasAdjoint := sorry_proof,
  abbrev † := ⟨0, xy'⟩ by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; infer_instance,
  abbrev ∂† := (0, dxy') by unfold adjointDifferential; symdiff; symdiff,
  abbrev ℛ := (xy.2, λ dxy' => (0,dxy')) by symdiff


--------------------------------------------------------------------------------
-- Prod.mk
--------------------------------------------------------------------------------

function_properties Prod.mk {X Y} [Vec X] [Vec Y] (x : X) (y : Y) : X×Y
argument (x,y) 
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := (dx, dy) by symdiff
argument x
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := (dx,0) by sorry_proof-- ,
  -- abbrev 𝒯 := ((x,y), (dx,0)) by symdiff
argument y
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := (0,dy) by sorry_proof -- ,
  -- abbrev 𝒯 := ((x,y), (0,dy)) by symdiff

function_properties Prod.mk {X Y} [SemiHilbert X] [SemiHilbert Y] (x : X) (y : Y) : X×Y
argument (x,y)
  hasAdjoint := sorry_proof,
  abbrev † := xy' by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† ℛ := dxy' by unfold adjointDifferential; symdiff; symdiff
argument x
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := dx'.1 by sorry_proof
argument y
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := dy'.2 by sorry_proof


--------------------------------------------------------------------------------
-- Neg.neg - (-·)
--------------------------------------------------------------------------------

function_properties Neg.neg {X} [Vec X] (x : X) : X
argument x
  isLin := sorry_proof, 
  isSmooth,
  abbrev ∂ 𝒯 := - dx by symdiff-- ,
  -- abbrev 𝒯 := (-x, -dx) by symdiff

function_properties Neg.neg {X} [SemiHilbert X] (x : X) : X
argument x
  hasAdjoint := sorry_proof, 
  abbrev † := - x' by sorry_proof,
  hasAdjDiff,
  abbrev ∂† ℛ := - dx' by unfold adjointDifferential; symdiff; symdiff


--------------------------------------------------------------------------------
-- HAdd.hAdd - (·+·)
--------------------------------------------------------------------------------

function_properties HAdd.hAdd {X} [Vec X]  (x y : X) : X
argument (x,y)
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := dx + dy by symdiff-- ,
  -- abbrev 𝒯 := (x+y, dx+dy) by symdiff
argument x
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := dx by sorry_proof-- ,
  -- abbrev 𝒯 := (x+y, dx) by symdiff
argument y
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := dy by sorry_proof-- ,
  -- abbrev 𝒯 := (x+y, dy) by symdiff


function_properties HAdd.hAdd {X} [SemiHilbert X] (x y : X) : X
argument (x,y)
  hasAdjoint := sorry_proof,
  abbrev † := (xy',xy') by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; (try infer_instance); sorry_proof,
  abbrev ∂† ℛ := (dxy', dxy') by unfold adjointDifferential; symdiff; symdiff
argument x 
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := dx' by sorry_proof
argument y
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := dy' by sorry_proof


--------------------------------------------------------------------------------
-- HSub.hSub - (·-·)
--------------------------------------------------------------------------------

function_properties HSub.hSub {X} [Vec X]  (x y : X) : X
argument (x,y)
  isLin := sorry_proof,
  abbrev ∂ 𝒯 := dx - dy by symdiff-- ,
  -- abbrev 𝒯 := (x-y, dx-dy) by symdiff
argument x
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := dx by sorry_proof-- ,
  -- abbrev 𝒯 := (x-y, dx) by symdiff
argument y
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := -dy by sorry_proof-- ,
  -- abbrev 𝒯 := (x-y,-dy) by symdiff

function_properties HSub.hSub {X} [SemiHilbert X] (x y : X) : X
argument (x,y)
  hasAdjoint := sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev † := (xy',-xy') by sorry_proof,
  abbrev ∂† ℛ := (dxy', -dxy') by unfold adjointDifferential; symdiff; symdiff
argument x 
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := dx' by sorry_proof
argument y
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := -dy' by sorry_proof


--------------------------------------------------------------------------------
-- HMul.hMul - (·*·)
--------------------------------------------------------------------------------

function_properties HMul.hMul {X} [Vec X] (x : ℝ) (y : X) : X
argument (x,y)
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := dx*y + x*dy by sorry_proof
argument x
  isLin := sorry_proof, 
  isSmooth,
  abbrev ∂ 𝒯 := dx*y by sorry_proof
argument y
  isLin := sorry_proof, 
  isSmooth,
  abbrev ∂ 𝒯 := x*dy by sorry_proof

function_properties HMul.hMul {X} [SemiHilbert X] (x : ℝ) (y : X) : X
argument y
  hasAdjoint := sorry_proof,
  abbrev † := x*y' by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; infer_instance,
  abbrev ∂† ℛ := x*dy' by unfold adjointDifferential; symdiff; symdiff
  
function_properties HMul.hMul {X} [Hilbert X] (x : ℝ) (y : X) : X
argument x
  hasAdjoint := sorry_proof,
  abbrev † := ⟪x',y⟫ by sorry_proof,
  hasAdjDiff := by sorry_proof, -- apply HasAdjDiffN.mk'; symdiff; infer_instance,
  abbrev ∂† ℛ := ⟪dx',y⟫ by unfold adjointDifferential; sorry_proof -- symdiff; symdiff
argument (x,y)
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† ℛ := (⟪dxy',y⟫, x*dxy') by unfold adjointDifferential; symdiff; sorry_proof


--------------------------------------------------------------------------------
-- Inner.innet - ⟪·,·⟫
--------------------------------------------------------------------------------

function_properties Inner.inner {X} [Hilbert X] (x y : X) : ℝ
argument (x,y)
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := ⟪dx,y⟫ + ⟪x,dy⟫ by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† ℛ := (dxy'*x, dxy'*y) by sorry_proof
argument x ..
  isLin := sorry_proof,
  isSmooth, 
  abbrev ∂ 𝒯 := ⟪dx,y⟫ by symdiff
argument x
  hasAdjoint := sorry_proof,
  abbrev † := x'*y by sorry_proof
argument y
  isLin := sorry_proof,
  isSmooth, 
  abbrev ∂ 𝒯 := ⟪x,dy⟫ by symdiff,
  hasAdjoint := sorry_proof,
  abbrev † := y'*x by sorry_proof


--------------------------------------------------------------------------------
-- Inner.normSqr - ∥·∥²
--------------------------------------------------------------------------------

function_properties Inner.normSqr {X} [Hilbert X] (x : X) : ℝ
argument x 
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := 2*⟪dx,x⟫ by sorry_proof,
  hasAdjDiff := sorry_proof,
  abbrev ∂† ℛ := 2*dx'*x by sorry_proof


--------------------------------------------------------------------------------
-- SmoothMap.val
--------------------------------------------------------------------------------

function_properties SmoothMap.val {X Y} [Vec X] [Vec Y] (f : X⟿Y) (x : X) : Y
argument (f,x)
  isSmooth := sorry_proof,
  abbrev ∂ := df x + ∂ f x dx by funext (f,x) (df,dx); simp; sorry_proof,
  abbrev 𝒯 := let (y,dy) := 𝒯 f x dx; (y, df x + dy) by unfold Smooth.tangentMap; symdiff
argument f
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := df x by symdiff 
argument x 
  isSmooth := sorry_proof,
  abbrev ∂ := ∂ f x dx by unfold Smooth.differential; symdiff,
  abbrev 𝒯 := 𝒯 f x dx by unfold Smooth.tangentMap; symdiff
  

--------------------------------------------------------------------------------
-- SmoothMap.mk'
--------------------------------------------------------------------------------

-- instance SmoothMap.mk'.arg_f.prolongation.isSmoothT {X Y W} [Vec X] [Vec Y] [Vec W] 
--   (f : W → X → Y) [IsSmoothNT 2 f]
--   : IsSmoothT (λ w => λ x ⟿ f w x) := sorry_proof

-- instance SmoothMap.mk'.arg_f.prolongation.diff_simp {X Y W} [Vec X] [Vec Y] [Vec W] 
--   (f : W → X → Y) [IsSmoothNT 2 f]
--   : ∂ (λ w => λ x ⟿ f w x) 
--     =
--     λ w dw => λ x ⟿ ∂ f w dw x:= sorry_proof


--------------------------------------------------------------------------------
-- LinMap.val
--------------------------------------------------------------------------------

function_properties LinMap.val {X Y} [Vec X] [Vec Y] (f : X⊸Y) (x : X) : Y
argument (f,x)
  isSmooth := sorry_proof,
  abbrev ∂ 𝒯 := df x + f dx by funext (f,x) (df,dx); simp; sorry_proof
argument f ..
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := df x by symdiff 
argument x 
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ 𝒯 := f dx by symdiff


--------------------------------------------------------------------------------
-- LinMap.mk'
--------------------------------------------------------------------------------

-- instance SmoothMap.mk'.arg_f.prolongation.isSmoothT {X Y W} [Vec X] [Vec Y] [Vec W] 
--   (f : W → X → Y) [IsSmoothNT 2 f]
--   : IsSmoothT (λ w => λ x ⟿ f w x) := sorry_proof

-- instance SmoothMap.mk'.arg_f.prolongation.diff_simp {X Y W} [Vec X] [Vec Y] [Vec W] 
--   (f : W → X → Y) [IsSmoothNT 2 f]
--   : ∂ (λ w => λ x ⟿ f w x) 
--     =
--     λ w dw => λ x ⟿ ∂ f w dw x:= sorry_proof
