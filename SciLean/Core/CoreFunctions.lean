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

function_properties Neg.neg {X} [Vec X] (x : X) : X
argument x
  isLin := sorry_proof, 
  isSmooth,
  abbrev ∂ := - dx by symdiff
  -- abbrev 𝒯 := (-x, -dx) by symdiff

function_properties Neg.neg {X} [SemiHilbert X] (x : X) : X
argument x
  hasAdjoint := sorry_proof, 
  abbrev † := - x' by sorry_proof,
  hasAdjDiff,
  abbrev ∂† := - dx' by unfold adjointDifferential; symdiff; symdiff
  --abbrev ℛ := (-x, λ dx' => - dx') by symdiff

--------------------------------------------------------------------------------

function_properties HAdd.hAdd {X} [Vec X]  (x y : X) : X
argument (x,y)
  isLin := sorry_proof,
  isSmooth,
  abbrev ∂ := dx + dy by symdiff
argument x ..
  isSmooth := sorry_proof,
  def ∂ := dx by sorry_proof
argument y
  isSmooth := sorry_proof,
  def ∂ := dy by sorry_proof

function_properties HAdd.hAdd {X} [SemiHilbert X] (x y : X) : X
argument (x,y)
  hasAdjoint := sorry_proof,
  abbrev † := (xy',xy') by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† := (dxy', dxy') by unfold adjointDifferential; symdiff; symdiff
argument x 
  hasAdjDiff := sorry_proof,
  abbrev ∂† := dx' by sorry_proof
argument y
  hasAdjDiff := sorry_proof,
  abbrev ∂† := dy' by sorry_proof

--------------------------------------------------------------------------------

function_properties HSub.hSub {X} [Vec X]  (x y : X) : X
argument (x,y)
  isLin := sorry_proof,
  abbrev ∂ := dx - dy by symdiff
argument x ..
  isSmooth := sorry_proof,
  def ∂ := dx by sorry_proof
argument y
  isSmooth := sorry_proof,
  def ∂ := -dy by sorry_proof

function_properties HSub.hSub {X} [SemiHilbert X] (x y : X) : X
argument (x,y)
  hasAdjoint := sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev † := (xy',-xy') by sorry_proof,
  abbrev ∂† := (dxy', -dxy') by unfold adjointDifferential; symdiff; symdiff
argument x 
  hasAdjDiff := sorry_proof,
  abbrev ∂† := dx' by sorry_proof
argument y
  hasAdjDiff := sorry_proof,
  abbrev ∂† := -dy' by sorry_proof

--------------------------------------------------------------------------------

function_properties HMul.hMul {X} [Vec X] (x : ℝ) (y : X) : X
argument (x,y)
  isSmooth := sorry_proof,
  abbrev ∂ := dx*y + x*dy by sorry_proof
argument x ..
  isLin := sorry_proof, 
  isSmooth,
  def ∂ := dx*y by sorry_proof
argument y
  isLin := sorry_proof, 
  isSmooth,
  def ∂ := x*dy by sorry_proof

function_properties HMul.hMul {X} [SemiHilbert X] (x : ℝ) (y : X) : X
argument y
  hasAdjoint := sorry_proof,
  abbrev † := x*y' by sorry_proof
  
function_properties HMul.hMul {X} [Hilbert X] (x : ℝ) (y : X) : X
argument x
  hasAdjoint := sorry_proof,
  abbrev † := ⟪x',y⟫ by sorry_proof
argument (x,y)
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† := (⟪dxy',y⟫, x*dxy') by unfold adjointDifferential; symdiff; sorry_proof

--------------------------------------------------------------------------------

function_properties Inner.inner {X} [Hilbert X] (x y : X) : ℝ
argument (x,y)
  isSmooth := sorry_proof,
  abbrev ∂ := ⟪dx,y⟫ + ⟪x,dy⟫ by sorry_proof,
  hasAdjDiff := by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† := (dxy'*x, dxy'*y) by sorry_proof
argument x ..
  isLin := sorry_proof,
  isSmooth, 
  abbrev ∂ := ⟪dx,y⟫ by symdiff
argument x
  hasAdjoint := sorry_proof,
  abbrev † := x'*y by sorry_proof
argument y
  isLin := sorry_proof,
  isSmooth, 
  abbrev ∂ := ⟪x,dy⟫ by symdiff,
  hasAdjoint := sorry_proof,
  abbrev † := y'*x by sorry_proof
