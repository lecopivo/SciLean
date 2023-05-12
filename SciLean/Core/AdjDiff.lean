import SciLean.Core.Defs
import SciLean.Core.HasAdjDiff
import SciLean.Core.Adjoint
import SciLean.Core.Differential
import SciLean.Core.Integral

namespace SciLean

variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z] 
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι κ : Type} [EnumType ι] [EnumType κ]

syntax "∂† " diffBinder ", " term:66 : term
syntax "∂† " "(" diffBinder ")" ", " term:66 : term
macro_rules
| `(∂† $x:ident, $f) =>
  `(∂† λ $x => $f)
| `(∂† $x:ident : $type:term, $f) =>
  `(∂† λ $x : $type => $f)
| `(∂† $x:ident := $val:term, $f) =>
  `((∂† λ $x => $f) $val)
| `(∂† $x:ident := $val:term ; $dir:term, $f) =>
  `((∂† λ $x => $f) $val $dir)
| `(∂† ($b:diffBinder), $f) =>
  `(∂† $b, $f)

@[app_unexpander adjointDifferential] def unexpandAdjointDifferential : Lean.PrettyPrinter.Unexpander

  | `($(_) $f:term $x $dx $y $ys*) =>
    match f with
    | `(fun $x':ident => $b:term) => `((∂† $x':ident:=$x;$dx, $b) $y $ys*)
    | _  => `(∂† $f:term $x:term $dx $y $ys*)

  | `($(_) $f:term $x $dx) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂† ($x':ident:=$x;$dx), $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∂† ($x':ident:=$x;$dx), $b)
    | _  => `(∂† $f:term $x $dx)

  | `($(_) $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂† ($x':ident:=$x), $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∂† ($x':ident:=$x), $b)
    | _  => `(∂† $f:term $x)

  | `($(_) $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∂† $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∂† ($x' : $ty), $b)
    | _  => `(∂† $f)

  | _  => throw ()


-- Notation 
-- ∇ s, f s         --> ∇ λ s => f s
-- ∇ s : ℝ, f s     --> ∇ λ s : ℝ => f s
-- ∇ s := t, f s    --> (∇ λ s => f s) t
syntax "∇ " diffBinder ", " term:66 : term
syntax "∇ " "(" diffBinder ")" ", " term:66 : term
macro_rules 
| `(∇ $x:ident, $f) =>
  `(∇ λ $x => $f)
| `(∇ $x:ident : $type:term, $f) =>
  `(∇ λ $x : $type => $f)
| `(∇ $x:ident := $val:term, $f) =>
  `((∇ λ $x => $f) $val)
| `(∇ ($b:diffBinder), $f) =>
  `(∇ $b, $f)

@[app_unexpander gradient] def unexpandGradient : Lean.PrettyPrinter.Unexpander

  | `($(_) $f:term $x $y $ys*) =>
    match f with
    | `(fun $x':ident => $b:term) => `((∇ $x':ident:=$x, $b) $y $ys*)
    | _  => `(∇ $f:term $x $y $ys*)

  | `($(_) $f:term $x) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ ($x':ident:=$x), $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∇ ($x':ident:=$x), $b)
    | _  => `(∇ $f:term $x)

  | `($(_) $f:term) =>
    match f with
    | `(fun $x':ident => $b:term) => `(∇ $x':ident, $b)
    | `(fun ($x':ident : $ty) => $b:term) => `(∇ ($x' : $ty), $b)
    | _  => `(∇ $f)

  | _  => throw ()


variable (f : X → ℝ) (x : X)

#check ∇ f
#check ∇ x', f x'
#check ∇ x':=x, f x'


variable {α β γ : Type}
variable {X Y Z : Type} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
variable {Y₁ Y₂ : Type} [SemiHilbert Y₁] [SemiHilbert Y₂]
variable {ι : Type} [EnumType ι]


@[fun_trans_rule]
theorem adjointDifferential.rule_id (X) [SemiHilbert X]
  : ∂† (λ x : X => x)
    =
    λ x dx' => dx' := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_const (Y : Type) [SemiHilbert Y] (x : X)
  : ∂† (λ y : Y => x)
    =
    λ y dy' => 0 := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_comp
  (f : Y → Z) [HasAdjDiff f]
  (g : X → Y) [HasAdjDiff g]
  : ∂† (λ x : X => f (g x))
    =
    λ x dx' => ∂† g x (∂† f (g x) dx') := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_pi
  (f : ι → X → Y) [∀ a, HasAdjDiff (f a)]
  : ∂† (λ (g : ι → X) (i : ι) => f i (g i))
    =
    λ g dg' i => ∂† (f i) (g i) (dg' i) := sorry

theorem adjointDifferential.rule_const' 
  : ∂† (λ (x : X) (i : ι) => x)
    =
    λ x dx' => ∑ i, dx' i := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_swap 
  (f : ι → X → Y) [∀ i, HasAdjDiff (f i)]
  : ∂† (λ (x : X) (i : ι) => f i x)
    =
    λ x dx' => ∑ i, ∂† (f i) x (dx' i) := 
by 
  rw[adjointDifferential.rule_comp (λ (g : ι → X) (i : ι) => f i (g i)) (λ x i => x)]
  simp[adjointDifferential.rule_pi, adjointDifferential.rule_const']
  done

@[fun_trans_rule]
theorem adjointDifferential.rule_eval (X) [SemiHilbert X] (i : ι)
  : ∂† (λ (f : ι → X) => f i)
    =
    λ f df' i' => [[i=i']] • df' := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_prodMk 
  (f : X → Y) [HasAdjDiff f]
  (g : X → Z) [HasAdjDiff g]
  : ∂† (λ x => (f x, g x))
    =
    λ x dx' => 
      ∂† f x dx'.1 + ∂† g x dx'.2 := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_letBinop 
  (f : X → Y → Z) [HasAdjDiff λ xy : X×Y => f xy.1 xy.2]
  (g : X → Y) [HasAdjDiff g]
  : ∂† (λ (x : X) => let y := g x; f x y)
    =
    λ x dx' =>
      let dxy := ∂† (λ xy : X×Y => f xy.1 xy.2) (x, g x) dx'
      dxy.1 + ∂† g x dxy.2 := sorry

@[fun_trans_rule]
theorem adjointDifferential.rule_letComp 
  (f : Y → Z) [HasAdjDiff f]
  (g : X → Y) [HasAdjDiff g]
  : ∂† (λ (x : X) => let y := g x; f y)
    =
    λ x dx' =>
      let dy' := ∂† f (g x) dx'
      ∂† g x dy' 
  := sorry

@[fun_trans]
theorem adjointDifferential.rule_fst (X Y) [SemiHilbert X] [SemiHilbert Y]
  : ∂† (λ (xy : X×Y) => xy.1)
    =
    λ xy dxy' => (dxy', 0) := sorry

@[fun_trans]
theorem adjointDifferential.rule_snd (X Y) [SemiHilbert X] [SemiHilbert Y]
  : ∂† (λ (xy : X×Y) => xy.2)
    =
    λ xy dxy' => (0, dxy') := sorry

/--

-/
@[fun_trans_rule]
theorem adjointDifferential.rule_piComp [Nonempty κ]
  (f : κ → (ι → X) → X → Y) [∀ j, HasAdjDiff (λ (g,x) => f j g x)] 
  (h : κ → ι) [IsInv h]
  : ∂† (λ (g : ι → X) (j : κ) => f j g (g (h j)))
    =
    λ g dg' i => 
      let dg₁ := λ i' => ∂† (λ x => f (h⁻¹ i') g x) (g i') (dg' (h⁻¹ i'))
      let dg₂ := ∂† (λ (g' : ι → X) (j : κ) => f j g' (g (h j))) g dg'
      dg₁ i + dg₂ i
  := sorry

theorem adjointDifferential.structure_rule.Prod 
  {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : X → Y → X×Y → Z) [HasAdjDiff λ (x,y,xy) => f x y xy]
  : ∂† (λ xy : X×Y => f xy.1 xy.2 xy)
    =
    λ xy dz => 
      let dx  := ∂† (λ x' => f x' xy.2 xy) xy.1 dz
      let dy  := ∂† (λ y' => f xy.1 y' xy) xy.2 dz
      let dxy := ∂† (λ xy' => f xy.1 xy.2 xy') xy dz
      (dx,dy) + dxy
  := sorry

--------------------------------------------------------------------------------
-- Reverse Differential Rules
--------------------------------------------------------------------------------

@[fun_trans_rule]
theorem reverseDifferential.rule_id (X) [SemiHilbert X]
  : ℛ (λ x : X => x)
    =
    λ x => (x , λ dx' => dx') := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_const (Y : Type) [SemiHilbert Y] (x : X)
  : ℛ (λ y : Y => x)
    =
    λ y => (x, λ dy' => 0) := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_comp
  (f : Y → Z) [HasAdjDiff f]
  (g : X → Y) [HasAdjDiff g]
  : ℛ (λ x : X => f (g x))
    =
    λ x => 
      let Ry := ℛ g x
      let Rz := ℛ f Ry.1
      (Rz.1, λ dx' => Ry.2 (Rz.2 dx')) := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_pi
  (f : ι → X → Y) [∀ a, HasAdjDiff (f a)]
  : ℛ (λ (g : ι → X) (i : ι) => f i (g i))
    =
    λ g => 
      let Rf := λ i => ℛ (f i) (g i)
      (λ i => (Rf i).1, λ dg' i => (Rf i).2 (dg' i)) := sorry

theorem reverseDifferential.rule_const' 
  : ℛ (λ (x : X) (i : ι) => x)
    =
    λ x => (λ i => x, λ dx' => ∑ i, dx' i) := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_swap 
  (f : ι → X → Y) [∀ i, HasAdjDiff (f i)]
  : ℛ (λ (x : X) (i : ι) => f i x)
    =
    λ x => 
      let Rf := λ i => ℛ (f i) x
      (λ i => (Rf i).1, λ dx' => ∑ i, (Rf i).2 (dx' i)) := 
by 
  rw[reverseDifferential.rule_comp (λ (g : ι → X) (i : ι) => f i (g i)) (λ x i => x)]
  simp[reverseDifferential.rule_pi, reverseDifferential.rule_const']
  done

@[fun_trans_rule]
theorem reverseDifferential.rule_eval (X) [SemiHilbert X] (i : ι)
  : ℛ (λ (f : ι → X) => f i)
    =
    λ f => (f i, λ df' i' => [[i=i']] • df') := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_prodMk 
  (f : X → Y) [HasAdjDiff f]
  (g : X → Z) [HasAdjDiff g]
  : ℛ (λ x => (f x, g x))
    =
    λ x => 
      let Ry := ℛ f x
      let Rz := ℛ g x
      ((Ry.1, Rz.1), λ dx' => Ry.2 dx'.1 + Rz.2 dx'.2) := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_letBinop 
  (f : X → Y → Z) [HasAdjDiff λ xy : X×Y => f xy.1 xy.2]
  (g : X → Y) [HasAdjDiff g]
  : ℛ (λ (x : X) => let y := g x; f x y)
    =
    λ x =>
      let Ry := ℛ g x
      let Rz := ℛ (λ xy : X×Y => f xy.1 xy.2) (x, Ry.1)
      (Rz.1, λ dx' => 
               let dxy := Rz.2 dx'
               dxy.1 + Ry.2 dxy.2)
  := sorry

@[fun_trans_rule]
theorem reverseDifferential.rule_letComp 
  (f : Y → Z) [HasAdjDiff f]
  (g : X → Y) [HasAdjDiff g]
  : ℛ (λ (x : X) => let y := g x; f y)
    =
    λ x =>
      let Ry := ℛ g x
      let Rz := ℛ f Ry.1
      (Rz.1, λ dx' => Ry.2 (Rz.2 dx'))
  := sorry

@[fun_trans]
theorem reverseDifferential.rule_fst (X Y) [SemiHilbert X] [SemiHilbert Y]
  : ℛ (λ (xy : X×Y) => xy.1)
    =
    λ xy => (xy.1, λ dxy' => (dxy', 0)) := sorry

@[fun_trans]
theorem reverseDifferential.rule_snd (X Y) [SemiHilbert X] [SemiHilbert Y]
  : ℛ (λ (xy : X×Y) => xy.2)
    =
    λ xy => (xy.2, λ dxy' => (0, dxy')) := sorry


theorem reverseDifferential.structure_rule.Prod 
  {X Y Z} [SemiHilbert X] [SemiHilbert Y] [SemiHilbert Z]
  (f : X → Y → X×Y → Z) [HasAdjDiff λ (x,y,xy) => f x y xy]
  : ℛ (λ xy : X×Y => f xy.1 xy.2 xy)
    =
    λ xy => 
      let Rz  := ℛ (λ xyxy : X×Y×(X×Y) => f xyxy.1 xyxy.2.1 xyxy.2.2) (xy.1,xy.2,xy)
      (Rz.1, λ dz => 
               let dxdydxy := Rz.2 dz
               (dxdydxy.1, dxdydxy.2.1) + dxdydxy.2.2)
  := sorry


#exit


instance (f : X → Y) [HasAdjDiff f] (x : X) : IsLin (∂† f x) := sorry

----------------------------------------------------------------------


@[simp ↓, diff]
theorem id.arg_x.adjDiff_simp
  : ∂† (λ x : X => x) = λ x dx => dx := by symdiff; simp[adjointDifferential]; done

@[simp ↓, diff]
theorem const.arg_x.adjDiff_simp 
  : ∂† (λ (x : X) (i : ι) => x) = λ x f => ∑ i, f i := by simp[adjointDifferential]; done

@[simp ↓, diff]
theorem const.arg_y.adjDiff_simp (x : X)
  : ∂† (λ (y : Y) => x) = (λ y dy' => (0 : Y)) := by simp[adjointDifferential]; done

@[simp ↓ low-4, diff low-4]
theorem swap.arg_y.adjDiff_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiffT (f i)]
  : ∂† (λ x y => f y x) = (λ x dx' => ∑ i, (∂† (f i) x) (dx' i)) := 
by 
  have := λ i => (inst i).1
  have := λ i => (inst i).2

  simp[adjointDifferential]; done

@[simp ↓ low-3, diff low-3]
theorem subst.arg_x.adjDiff_simp
  (f : X → Y → Z) [instf : HasAdjDiffNT 2 f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x)) 
    = 
    λ x dz =>
      let (y,dg') := ℛ g x
      -- let (dx,dy) := ∂† (uncurryN 2 f) (x,y) dz
      -- dx + dg' dy
      (∂† (λ x' => f x' y)) x dz
      +
      dg' (∂† (f x) y dz)
    := 
by 
  have := instg.1
  have := instg.2
  have := instf.1
  -- these follow from instf.proof.2
  have : ∀ x y, HasAdjointT (λ dx => ∂ f x dx y) := sorry_proof
  have : ∀ x y, HasAdjointT (λ dy => ∂ (f x) y dy) := sorry_proof

  unfold adjointDifferential -- reverseDifferential, tangentMap, -comp.arg_x.parm1.adj_simp]
  sorry -- symdiff
    --sorry_proof
  -- simp (config := {singlePass := true})
  -- done

@[simp ↓ low-2, diff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      -- let (dx,dy) := ∂† (uncurryN 2 (λ x y => f x y a)) (x,y) dz
      -- dx + dg' dy
      (∂† (λ x' => f x' y a)) x dz
      +
      dg' (∂† (λ y' => f x y' a) y dz)
    := 
by 
  rw[subst.arg_x.adjDiff_simp (λ x y => f x y a) g]
  done

@[simp ↓ low-2, diff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a b) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      (∂† (λ x' => f x' y a b)) x dz
      +
      dg' (∂† (λ y' => f x y' a b) y dz)
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, diff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f x (g x) a b c) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      (∂† (λ x' => f x' y a b c)) x dz
      +
      dg' (∂† (λ y' => f x y' a b c) y dz)
    := 
by 
  apply subst.arg_x.adjDiff_simp (λ x y => f x y a b c) g
  done

@[simp ↓ low-1, diff low-1, simp_guard g (λ x => x)]
theorem comp.arg_x.adjDiff_simp
  (f : Y → Z) [instf : HasAdjDiffT f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ∂† (λ x => f (g x)) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      dg' ((∂† f y) dz) 
  := by simp; done

@[simp ↓ low-2, diff low-2, simp_guard g₁ Prod.fst, g₂ Prod.snd]
theorem diag.arg_x.adjDiff_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† λ y₁' => f y₁' y₂) y₁ dz)
      +
      dg₂' ((∂† λ y₂' => f y₁ y₂') y₂ dz)
    := 
by
  rw[subst.arg_x.adjDiff_simp]
  simp only [hold,reverseDifferential]
  funext x dz
  rw[comp.arg_x.adjDiff_simp (λ y₁ => f y₁ (g₂ x))]
  simp only [reverseDifferential]
  done

@[simp ↓ low, diff low]
theorem eval.arg_f.adjDiff_simp
  (i : ι)
  : ∂† (λ (f : ι → X) => f i) 
    = 
    (λ f df' j => ([[i = j]] • df' : X))
:= sorry

@[simp ↓ low-1, diff low-1]
theorem eval.arg_x.parm1.adjDiff_simp
  (f : X → ι → Z) [HasAdjDiff f]
  : ∂† (λ x => f x i) 
    = 
    (λ x dx' => (∂† f x) (λ j => ([[i = j]] • dx' : Z)))
:= 
by 
  rw [comp.arg_x.adjDiff_simp (λ (x : ι → Z) => x i) f]
  simp[reverseDifferential]


--------------------------------------------------------
-- These theorems are problematic when used with simp --


@[simp ↓ low-1, diff low-1]
theorem comp.arg_x.parm1.adjDiff_simp
  (a : α) 
  (f : Y → α → Z) [HasAdjDiff λ y => f y a]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      dg' ((∂† (hold λ y => f y a)) y dz)
:= by 
  rw[subst.arg_x.parm1.adjDiff_simp]
  simp[-subst.arg_x.parm1.adjDiff_simp,hold]
  done

@[simp ↓ low-1, diff low-1]
theorem comp.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y → α → β → Z) [HasAdjDiff λ y => f y a b]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a b) 
    = 
    λ x dz => 
      let (y,dg') := ℛ g x
      dg' ((∂† (hold λ y => f y a b)) y dz)
:= by 
  rw[subst.arg_x.parm2.adjDiff_simp]
  simp[-subst.arg_x.parm2.adjDiff_simp,hold]
  done

@[simp ↓ low-1, diff low-1]
theorem comp.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y → α → β → γ → Z) [HasAdjDiff λ y => f y a b c]
  (g : X → Y) [HasAdjDiff g]
  : 
    ∂† (λ x => f (g x) a b c) 
    = 
    λ x dx' => 
      let (y,dg') := ℛ g x
      dg' ((∂† (hold λ y => f y a b c)) y dx')
:= by 
  rw[subst.arg_x.parm3.adjDiff_simp]
  simp[-subst.arg_x.parm3.adjDiff_simp,hold]
  done


-- TODO: fix this!!!
example (a : α) (f : Y₁ → Y₂ → α → Z) [IsSmoothT λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [hg : IsSmoothT g₁] : IsSmoothT (λ x y => f (g₁ x) y a) := by (try infer_instance); admit


@[simp ↓ low-1, diff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm1.adjDiff_simp
  (a : α)
  (f : Y₁ → Y₂ → α → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a)
    = 
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† (hold λ y₁' => f y₁' y₂ a)) y₁ dz)
      +
      dg₂' ((∂† (hold λ y₂' => f y₁ y₂' a)) y₂ dz)
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a) g₁ g₂)
  
@[simp ↓ low-1, diff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm2.adjDiff_simp
  (a : α) (b : β)
  (f : Y₁ → Y₂ → α → β → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a b]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a b)
    = 
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† (hold λ y₁' => f y₁' y₂ a b)) y₁ dz)
      +
      dg₂' ((∂† (hold λ y₂' => f y₁ y₂' a b)) y₂ dz)
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a b) g₁ g₂)
  done

@[simp ↓ low-1, diff low-1] -- try to avoid using this theorem
theorem diag.arg_x.parm3.adjDiff_simp
  (a : α) (b : β) (c : γ)
  (f : Y₁ → Y₂ → α → β → γ → Z) [HasAdjDiffNT 2 λ y₁ y₂ => f y₁ y₂ a b c]
  (g₁ : X → Y₁) [HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ∂† (λ x => f (g₁ x) (g₂ x) a b c)
    = 
    λ x dz => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      dg₁' ((∂† (hold λ y₁' => f y₁' y₂ a b c)) y₁ dz)
      +
      dg₂' ((∂† (hold λ y₂' => f y₁ y₂' a b c)) y₂ dz)
:= by 
  (apply diag.arg_x.adjDiff_simp (λ y₁ y₂ => f y₁ y₂ a b c) g₁ g₂)
  done

----------------------------------------------------------------------



@[simp ↓, diff]
theorem id.arg_x.revDiff_simp
  : ℛ (λ x : X => x) = λ x => (x, λ x => x) := by simp[reverseDifferential]; done

@[simp ↓, diff]
theorem const.arg_x.revDiff_simp 
  : ℛ (λ (x : X) (i : ι) => x) 
    = 
    λ x => ((λ i => x), (λ f => ∑ i, f i))
  := by simp[reverseDifferential]; done

@[simp ↓, diff]
theorem const.arg_y.revDiff_simp (x : X)
  : ℛ (λ (y : Y) => x) 
    =
    λ y => 
      (x, (λ dy' => 0))
  := by simp[reverseDifferential]; done

@[simp ↓ low-4, diff low-4]
theorem swap.arg_y.revDiff_simp
  (f : ι → X → Z) [inst : ∀ i, HasAdjDiffT (f i)]
  : ∂† (λ x y => f y x) = (λ x dx' => ∑ i, (∂† (f i) x) (dx' i)) := 
by 
  have := λ i => (inst i).1
  have := λ i => (inst i).2

  simp[adjointDifferential]; done

@[simp ↓ low-3, diff low-3, simp_guard g (λ x => x)]
theorem subst.arg_x.revDiff_simp
  (f : X → Y → Z) [instf : HasAdjDiffNT 2 f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x)) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 f) (x,y)
      (z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy)
      
    := 
by 
  have := instg.1
  have := instg.2
  have := instf.1

  funext x;
  unfold reverseDifferential
  rw[subst.arg_x.adjDiff_simp]

  simp only [uncurryN, Prod.Uncurry.uncurry]
  simp only [hold, reverseDifferential]
  conv => (rhs; rw[diag.arg_x.adjDiff_simp])
  simp only [reverseDifferential, 
             Prod.fst.arg_xy.adjDiff_simp, 
             Prod.snd.arg_xy.adjDiff_simp,
             prod_add_elemwise, 
             add_zero, zero_add]
  done


@[simp ↓ low-2, diff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm1.revDiff_simp
  (a : α)
  (f : X → Y → α → Z) [HasAdjDiffNT 2 λ x y => f x y a]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x) a) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 (λ x y => f x y a)) (x,y)
      (z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy)
    := 
by 
  apply subst.arg_x.revDiff_simp (λ x y => f x y a) g
  done

@[simp ↓ low-2, diff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm2.revDiff_simp
  (a : α) (b : β)
  (f : X → Y → α → β → Z) [HasAdjDiffNT 2 λ x y => f x y a b]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x) a b) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 (λ x y => f x y a b)) (x,y)
      (z, λ dz' => 
           let (dx₁,dy) := df' dz'
           dx₁ + dg' dy)
    := 
by 
  apply subst.arg_x.revDiff_simp (λ x y => f x y a b) g
  done

@[simp ↓ low-2, diff low-2, simp_guard g (λ x => x)]
theorem subst.arg_x.parm3.revDiff_simp
  (a : α) (b : β) (c : γ)
  (f : X → Y → α → β → γ → Z) [HasAdjDiffNT 2 λ x y => f x y a b c]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f x (g x) a b c) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ (uncurryN 2 (λ x y => f x y a b c)) (x,y)
      (z, λ dz' => let (dx₁,dy) := df' dz'; dx₁ + dg' dy)
    := 
by 
  apply subst.arg_x.revDiff_simp (λ x y => f x y a b c) g
  done


-- @[simp ↓ low-10, diff low-10]
theorem uncurryN2.arg_x.diff_simp
  (f : X → Y → Z) [HasAdjDiffNT 2 f]
  : ∂† (uncurryN 2 f) 
    =
    λ (x,y) dz =>
      (∂† (λ x' => f x' y) x dz, ∂† (λ y' => f x y') y dz)
  := sorry_proof

@[simp ↓ low-1, diff low-1]
theorem comp.arg_x.revDiff_simp
  (f : Y → Z) [instf : HasAdjDiffT f]
  (g : X → Y) [instg : HasAdjDiffT g]
  : ℛ (λ x => f (g x)) 
    = 
    λ x => 
      let (y,dg') := ℛ g x
      let (z,df') := ℛ f y
      (z, λ dz => dg' (df' dz)) := 
by 
  unfold reverseDifferential
  simp only [comp.arg_x.adjDiff_simp]
  simp only [reverseDifferential]
  done

@[simp ↓ low-2, diff low-2]
theorem diag.arg_x.revDiff_simp
  (f : Y₁ → Y₂ → Z) [HasAdjDiffNT 2 f]
  (g₁ : X → Y₁) [hg : HasAdjDiffT g₁]
  (g₂ : X → Y₂) [HasAdjDiffT g₂]
  : ℛ (λ x => f (g₁ x) (g₂ x)) 
    = 
    λ x => 
      let (y₁,dg₁') := ℛ g₁ x
      let (y₂,dg₂') := ℛ g₂ x
      let (z, df') := ℛ (uncurryN 2 f) (y₁,y₂)
      (z, λ dz => let (dy₁,dy₂) := df' dz; dg₁' dy₁ + dg₂' dy₂)
      -- dg₁' ((∂† λ y₁ => f y₁ y₂) y₁ (h₁ ▸ h₂ ▸ dx'))
      -- +
      -- dg₂' ((∂† λ y₂ => f y₁ y₂) y₂ (h₂ ▸ h₁ ▸ dx'))
    := 
by
  unfold reverseDifferential
  funext x
  simp only [uncurryN, Prod.Uncurry.uncurry]
  conv => lhs; enter [2,dz]; rw [diag.arg_x.adjDiff_simp]
  conv => rhs; enter [2,dz]; rw [diag.arg_x.adjDiff_simp]
  simp only [reverseDifferential,             
             Prod.fst.arg_xy.adjDiff_simp, 
             Prod.snd.arg_xy.adjDiff_simp, 
             prod_add_elemwise, 
             add_zero, zero_add]
  done

@[simp ↓ low, diff low]
theorem eval.arg_f.revDiff_simp
  (i : ι)
  : ℛ (λ (f : ι → X) => f i) 
    = 
    λ f => (f i, (λ dx j => ([[i=j]] • dx : X)))
  := 
by 
  simp[reverseDifferential,adjointDifferential]; done

@[simp ↓ low-1, diff low-1]
theorem eval.arg_x.parm1.revDiff_simp
  (f : X → ι → Z) [HasAdjDiff f] (i : ι)
  : ℛ (λ x => f x i)
    = 
    λ x =>
      let (fx, df') := ℛ f x
      (fx i, 
      λ dz => df' (λ j => ([[i=j]] • dz)))
  := 
by 
  rw [comp.arg_x.revDiff_simp (λ (x : ι → Z) => x i) f]
  simp[reverseDifferential,adjointDifferential]


-- @[simp ↓]
-- theorem subst.arg_x.revDiff_simp'''
--   (f : X → Y → Z) [IsSmooth f]
--   [instfx : ∀ y, HasAdjDiff λ x => f x y]
--   [instfy : ∀ x, HasAdjDiff (f x)]
--   (g : Y → X) [instg : HasAdjDiff g]
--   : ∂† (λ y => f (g y) y) 
--     = 
--     λ y dy' => 
--       (∂† (λ y' => f (g y) y')) y dy'
--       +
--       (∂† g y) (∂† (λ x => f x y) (g y) dy')
--     := 
-- by 
--   sorry








