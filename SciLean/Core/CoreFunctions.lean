-- import SciLean.Core.FunctionProperties
import SciLean.Core.AdjDiff
import SciLean.Core.Meta.FunctionProperty.Syntax
namespace SciLean

--------------------------------------------------------------------------------
-- Core bootstrapping theorems
--------------------------------------------------------------------------------

theorem differential.of_linear {X Y} [Vec X] [Vec Y] {f : X → Y} [IsLin f]
  : ∂ f = λ _ dx => f dx := sorry_proof

--------------------------------------------------------------------------------
-- Prod.fst - (·.1)
--------------------------------------------------------------------------------

function_properties Prod.fst {X Y : Type} [Vec X] [Vec Y] (xy : X×Y)
argument xy
  IsLin, IsSmooth,
  abbrev ∂ := λ dxy => dxy.1 by rw[differential.of_linear]; done,
  abbrev 𝒯 := λ dxy => (xy.1, dxy.1) by simp[tangentMap, differential.of_linear]; done

function_properties Prod.fst {X Y} [SemiHilbert X] [SemiHilbert Y] (xy : X×Y) : X
argument xy
  HasAdjoint,
  abbrev † := λ xy' => ⟨xy',0⟩ by sorry_proof,
  HasAdjDiff,
  abbrev ∂† := λ dxy' => (dxy', 0) by sorry_proof,
  abbrev ℛ := (xy.1, λ dxy' => (dxy', 0)) by sorry_proof


--------------------------------------------------------------------------------
-- Prod.snd - (·.2)
--------------------------------------------------------------------------------

function_properties Prod.snd {X Y : Type} [Vec X] [Vec Y] (xy : X×Y)
argument xy
  IsLin, IsSmooth,
  abbrev ∂ := λ dxy => dxy.2 by rw[differential.of_linear]; done,
  abbrev 𝒯 := λ dxy => (xy.2, dxy.2) by simp[tangentMap, differential.of_linear]; done

function_properties Prod.snd {X Y : Type} [SemiHilbert X] [SemiHilbert Y] (xy : X×Y) : X
argument xy
  HasAdjoint,
  abbrev † := λ xy' => ⟨0,xy'⟩ by sorry_proof,
  HasAdjDiff,
  abbrev ∂† := λ dxy' => (0,dxy') by sorry_proof,
  abbrev ℛ := (xy.2, λ dxy' => (0,dxy')) by sorry_proof


--------------------------------------------------------------------------------
-- Prod.mk
--------------------------------------------------------------------------------

function_properties Prod.mk {X Y : Type} [Vec X] [Vec Y] (x : X) (y : Y) : X×Y
argument (x,y) 
  IsLin, IsSmooth,
  abbrev ∂ := λ dx dy => (dx, dy) by sorry_proof,
  abbrev 𝒯 := λ dx dy => ((x,y),(dx, dy)) by sorry_proof
argument x
  IsSmooth,
  abbrev ∂ := λ dx => (dx,0) by sorry_proof,
  abbrev 𝒯 := λ dx => ((x,y), (dx,0)) by sorry_proof
argument y
  IsSmooth := by apply Prod.mk.arg_fstsnd.IsSmooth',
  abbrev ∂ := λ dy => (0,dy) by sorry_proof,
  abbrev 𝒯 := λ dy => ((x,y),(0,dy)) by sorry_proof

function_properties Prod.mk {X Y : Type} [SemiHilbert X] [SemiHilbert Y] (x : X) (y : Y) : X×Y
argument (x,y)
  HasAdjoint,
  abbrev † := λ xy' => xy' by sorry_proof,
  HasAdjDiff,
  abbrev ∂† := λ dxy' => dxy' by sorry_proof,
  abbrev ℛ := ((x,y), λ dxy' => dxy') by sorry_proof
argument x
  HasAdjDiff,
  abbrev ∂† := λ dx' => dx'.1 by sorry_proof,
  abbrev ℛ := ((x,y), λ dx' => dx'.1) by sorry_proof
argument y
  HasAdjDiff := by apply Prod.mk.arg_fstsnd.HasAdjDiff',
  abbrev ∂† := λ dy' => dy'.2 by sorry_proof,
  abbrev ℛ := ((x,y), λ dy' => dy'.2) by sorry_proof


--------------------------------------------------------------------------------
-- Neg.neg - (-·)
--------------------------------------------------------------------------------

function_properties Neg.neg {X : Type} [Vec X] (x : X) : X
argument x
  IsLin := sorry_proof, 
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => -dx by simp[differential.of_linear], 
  abbrev 𝒯 := λ dx => (-x, -dx) by simp[tangentMap,differential.of_linear]

function_properties Neg.neg {X} [SemiHilbert X] (x : X) : X
argument x
  HasAdjoint := sorry_proof, 
  abbrev † := λ x' => -x' by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => -dx' by sorry_proof,
  abbrev ℛ := (-x, λ dx' => -dx') by sorry_proof


--------------------------------------------------------------------------------
-- HAdd.hAdd - (·+·)
--------------------------------------------------------------------------------

function_properties HAdd.hAdd {X : Type} [Vec X] (x y : X) : X
argument (x,y)
  IsLin    := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx dy => dx + dy by sorry_proof,
  abbrev 𝒯 := λ dx dy => (x + y, dx + dy) by sorry_proof
argument x
  IsSmooth := by infer_instance,
  abbrev ∂ := λ dx => dx by sorry_proof,
  abbrev 𝒯 := λ dx => (x+y, dx) by sorry_proof
argument y
  IsSmooth := by apply HAdd.hAdd.arg_a4a5.IsSmooth',
  abbrev ∂ := λ dy => dy by sorry_proof,
  abbrev 𝒯 := λ dy => (x+y, dy) by sorry_proof

function_properties HAdd.hAdd {X : Type} [SemiHilbert X] (x y : X) : X
argument (x,y)
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  abbrev † := λ xy' => (xy', xy') by sorry,
  abbrev ∂† := λ dxy' => (dxy', dxy') by sorry,
  abbrev ℛ := (x+y, λ dxy' => (dxy', dxy')) by sorry
argument x
  HasAdjDiff := by infer_instance,
  abbrev ∂† := λ dx' => dx' by sorry,
  abbrev ℛ := (x+y, λ dx' => dx') by sorry
argument y
  HasAdjDiff := by apply HAdd.hAdd.arg_a4a5.HasAdjDiff',
  abbrev ∂† := λ dy' => dy' by sorry,
  abbrev ℛ := (x+y, λ dy' => dy') by sorry


--------------------------------------------------------------------------------
-- HSub.hSub - (·-·)
--------------------------------------------------------------------------------

function_properties HSub.hSub {X : Type} [Vec X] (x y : X) : X
argument (x,y)
  IsLin    := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx dy => dx - dy by sorry_proof,
  abbrev 𝒯 := λ dx dy => (x - y, dx - dy) by sorry_proof
argument x
  IsSmooth := by infer_instance,
  abbrev ∂ := λ dx => dx by sorry_proof,
  abbrev 𝒯 := λ dx => (x-y, dx) by sorry_proof
argument y
  IsSmooth := by apply HSub.hSub.arg_a4a5.IsSmooth',
  abbrev ∂ := λ dy => -dy by sorry_proof,
  abbrev 𝒯 := λ dy => (x-y, -dy) by sorry_proof

function_properties HSub.hSub {X : Type} [SemiHilbert X] (x y : X) : X
argument (x,y)
  HasAdjoint := sorry,
  HasAdjDiff := sorry,
  abbrev † := λ xy' => (xy', -xy') by sorry,
  abbrev ∂† := λ dxy' => (dxy', -dxy') by sorry,
  abbrev ℛ := (x+y, λ dxy' => (dxy', -dxy')) by sorry
argument x
  HasAdjDiff := by infer_instance,
  abbrev ∂† := λ dx' => dx' by sorry,
  abbrev ℛ := (x-y, λ dx' => dx') by sorry
argument y
  HasAdjDiff := by apply HSub.hSub.arg_a4a5.HasAdjDiff',
  abbrev ∂† := λ dy' => -dy' by sorry,
  abbrev ℛ := (x-y, λ dy' => -dy') by sorry


--------------------------------------------------------------------------------
-- SMul.sMul - (·•·)
--------------------------------------------------------------------------------

function_properties SMul.smul {X : Type} [Vec X] (x : ℝ) (y : X) : X
argument (x,y)
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx dy => dx•y + x•dy by sorry_proof,
  abbrev 𝒯 := λ dx dy => (x•y, dx•y + x•dy) by sorry_proof
argument x
  IsLin := sorry_proof, 
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => dx•y by sorry_proof,
  abbrev 𝒯 := λ dx => (x•y, dx•y) by sorry_proof
argument y
  IsLin := sorry_proof, 
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dy => x•dy by sorry_proof,
  abbrev 𝒯 := λ dy => (x•dy, x•dy) by sorry_proof

function_properties SMul.smul {X : Type} [SemiHilbert X] (x : ℝ) (y : X) : X
argument y
  HasAdjoint := sorry_proof,
  abbrev † := λ y' => x•y' by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dy' => x•dy' by sorry_proof,
  abbrev ℛ := (x•y, λ dy' => x•dy') by sorry_proof
  
function_properties SMul.smul {X : Type} [Hilbert X] (x : ℝ) (y : X) : X
argument (x,y)
  HasAdjDiff := sorry_proof, --  by apply HasAdjDiffN.mk'; symdiff; sorry_proof,
  abbrev ∂† := λ dxy' => (⟪dxy',y⟫, x•dxy') by sorry_proof,
  abbrev ℛ := (x•y, λ dxy' => (⟪dxy',y⟫, x•dxy')) by sorry_proof
argument x
  HasAdjoint := sorry_proof,
  abbrev † := λ x' => ⟪x',y⟫ by sorry_proof,
  HasAdjDiff := by sorry_proof, 
  abbrev ∂† := λ dx' => ⟪dx',y⟫ by sorry_proof,
  abbrev ℛ := (x•y, λ dx' => ⟪dx',y⟫) by sorry_proof


--------------------------------------------------------------------------------
-- HMul.hMul - (·*·)
--------------------------------------------------------------------------------

-- TODO: Generalize to any algebra with smooth multiplication
function_properties HMul.hMul (x y : ℝ)
argument (x,y)
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx dy => dx*y + x*dy by sorry_proof,
  abbrev 𝒯 := λ dx dy => (x*y, dx*y + x*dy) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dxy' => (dxy'*y, x*dxy') by sorry_proof,
  abbrev ℛ := (x*y, λ dxy' => (dxy'*y, x*dxy')) by sorry_proof
argument x
  IsLin := sorry_proof, 
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => dx*y by sorry_proof,
  abbrev 𝒯 := λ dx => (x*y, dx*y) by sorry_proof,
  HasAdjoint := sorry_proof,
  abbrev † := λ x' => x'*y by sorry_proof,
  HasAdjDiff := by sorry_proof, 
  abbrev ∂† := λ dx' => dx'*y by sorry_proof,
  abbrev ℛ := (x*y, λ dx' => dx'*y) by sorry_proof
argument y
  IsLin := sorry_proof, 
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dy => x*dy by sorry_proof,
  abbrev 𝒯 := λ dy => (x*dy, x*dy) by sorry_proof,
  HasAdjoint := sorry_proof,
  abbrev † := λ y' => x*y' by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dy' => x*dy' by sorry_proof,
  abbrev ℛ := (x*y, λ dy' => x*dy') by sorry_proof


--------------------------------------------------------------------------------
-- Inner.innet - ⟪·,·⟫
--------------------------------------------------------------------------------

function_properties SciLean.Inner.inner {X} [Hilbert X] (x y : X)
argument (x,y)
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx dy => ⟪dx,y⟫ + ⟪x,dy⟫ by sorry_proof,
  abbrev 𝒯 := λ dx dy => (⟪x,y⟫, ⟪dx,y⟫ + ⟪x,dy⟫) by sorry_proof,
  HasAdjDiff := sorry_proof, 
  abbrev ∂† := λ dxy' => (dxy'•x, dxy'•y) by sorry_proof,
  abbrev ℛ := (⟪x,y⟫, λ dxy' => (dxy'•x, dxy'•y)) by sorry_proof
argument x 
  IsLin := sorry_proof,
  IsSmooth := sorry_proof, 
  abbrev ∂ := λ dx => ⟪dx,y⟫ by sorry_proof,
  abbrev 𝒯 := λ dx => (⟪x,y⟫, ⟪dx,y⟫) by sorry_proof,
  HasAdjoint := sorry_proof,
  abbrev † := λ x' => x'•y by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => dx'•y by sorry_proof,
  abbrev ℛ := (⟪x,y⟫,λ dx' => dx'•y) by sorry_proof
argument y
  IsLin := sorry_proof,
  IsSmooth := sorry_proof, 
  abbrev ∂ := λ dy => ⟪x,dy⟫ by sorry_proof,
  abbrev 𝒯 := λ dy => (⟪x,y⟫, ⟪x,dy⟫) by sorry_proof,
  HasAdjoint := sorry_proof,
  abbrev † := λ y' => y'•x by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dy' => dy'•x by sorry_proof,
  abbrev ℛ := (⟪x,y⟫, λ dy' => dy'•x) by sorry_proof



--------------------------------------------------------------------------------
-- Inner.normSqr - ∥·∥²
--------------------------------------------------------------------------------

function_properties SciLean.Inner.normSqr {X : Type} [Hilbert X] (x : X) : ℝ
argument x 
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => 2*⟪dx,x⟫ by sorry_proof,
  abbrev 𝒯 := λ dx => (‖x‖², 2*⟪dx,x⟫) by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ dx' => (2*dx')•x by sorry_proof,
  abbrev ℛ := (‖x‖², λ dx' => (2*dx')•x) by sorry_proof


--------------------------------------------------------------------------------
-- sum - ∑
--------------------------------------------------------------------------------

function_properties Enumtype.sum {X ι : Type} [Vec X] [Enumtype ι] (f : ι → X) : X
argument f
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ df => sum df by sorry_proof,
  abbrev 𝒯 := λ df => (sum f, sum df) by sorry_proof


function_properties Enumtype.sum {X ι : Type} [SemiHilbert X] [Enumtype ι] (f : ι → X) : X
argument f
  HasAdjoint := sorry_proof,
  abbrev † := λ f' _ => f' by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ df' _ => df' by sorry_proof,
  abbrev ℛ := (sum f, λ df' _ => df') by sorry_proof


--------------------------------------------------------------------------------
-- SmoothMap.val
--------------------------------------------------------------------------------

function_properties SciLean.SmoothMap.toFun {X Y : Type} [Vec X] [Vec Y] (f : X⟿Y) (x : X) : Y
argument (f,x)
  IsSmooth := sorry_proof
  -- noncomputable abbrev ∂ := λ df dx => df x + ∂ f x dx by sorry_proof,
  -- noncomputable abbrev 𝒯 := λ df dx => let (y,dy) := 𝒯 f x dx; (y, df x + dy) by sorry_proof
argument f
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ df => df x by sorry_proof,
  abbrev 𝒯 := λ df => (f x, df x) by sorry_proof
argument x 
  IsSmooth := sorry_proof
  -- noncomputable abbrev ∂ := λ dx => ∂ f x dx by sorry_proof,
  -- noncomputable abbrev 𝒯 := λ dx => 𝒯 f x dx by sorry_proof


--------------------------------------------------------------------------------
-- SmoothMap.mk'
--------------------------------------------------------------------------------


-- TODO: Make this work!
-- function_properties SciLean.SmoothMap.mk {X Y : Type} [Vec X] [Vec Y] (f : X → Y) (hf : IsSmooth f)
-- argument f 
--   IsLin [IsLin λ tx => f tx.1 tx.2] := sorry_proof,
--   IsSmooth [IsSmooth λ tx => f tx.1 tx.2] := sorry_proof,
--   abbrev ∂ [IsSmooth λ tx => f tx.1 tx.2] := λ df => df by sorry_proof


--------------------------------------------------------------------------------
-- LinMap.val
--------------------------------------------------------------------------------

function_properties SciLean.LinMap.toFun {X Y : Type} [Vec X] [Vec Y] (f : X⊸Y) (x : X)
argument (f,x)
  IsSmooth := sorry_proof,
  abbrev ∂ := λ df dx => df x + f dx by sorry_proof,
  abbrev 𝒯 := λ df dx => (f x, df x + f dx) by sorry_proof
argument f 
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ df => df x by sorry_proof,
  abbrev 𝒯 := λ df => (f x, df x) by sorry_proof
argument x 
  IsLin := sorry_proof,
  IsSmooth := sorry_proof,
  abbrev ∂ := λ dx => f dx by sorry_proof,
  abbrev 𝒯 := λ dx => (f x, f dx) by sorry_proof

function_properties SciLean.LinMap.toFun {X Y ι : Type} [Enumtype ι] [FinVec X ι] [Hilbert Y] (f : X⊸Y) (x : X) : Y
argument f
  HasAdjoint := sorry_proof,
  abbrev † := λ f' => ⟨λ x' => ⟪x,x'⟫ • f', sorry_proof⟩ by sorry_proof,
  HasAdjDiff := sorry_proof,
  abbrev ∂† := λ df' => ⟨λ x' => ⟪x,x'⟫ • df', sorry_proof⟩ by sorry_proof,
  abbrev ℛ := (f x, λ df' => ⟨λ x' => ⟪x,x'⟫ • df', sorry_proof⟩) by sorry_proof


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

