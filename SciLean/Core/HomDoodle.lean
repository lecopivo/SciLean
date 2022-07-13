import SciLean.Core.Mor
import SciLean.Core.Fun
import SciLean.Core.Functions
import SciLean.Core.Hom.SmoothMap
import SciLean.Core.Hom.LinMap
import SciLean.Core.Obj.FinVec

set_option synthInstance.maxSize 2048

namespace SciLean

  namespace HomProps
  
    variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

    instance (P : Y → Prop) [Vec ((y : Y) ×' P y)] 
             (f : X → Y) [IsLin f] 
             (p : (x : X) → P (f x)) 
             : IsLin λ x => PSigma.mk (f x) (p x) := sorry

    instance (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)] : IsSmooth λ x => LinMap.mk (f x) := sorry

    -- noncomputable
    -- def smoothDiff (f : X ⟿ Y) : X ⟿ X ⊸ Y := 
    --   ⟨λ x => ⟨λ dx => ∂ f x dx, by infer_instance⟩, by infer_instance⟩

    function_properties PSigma.fst {X} {P : X → Prop} [Vec X] [Vec ((x : X) ×' P x)] (x : ((x : X) ×' P x)) : X
    argument x
      isLin := sorry,
      isSmooth, diff_simp

    instance : IsLin    λ (f : X⟿Y) => ∂ f.1 := sorry
    instance : IsSmooth λ (f : X⟿Y) => ∂ f.1 := sorry
    instance {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y]
      : HasAdjoint λ (f : X⟿Y) => λ x ⟿ λ dx ⊸ ∂ f.1 x dx := sorry
    

  end HomProps

  --------------------------------------------------------------------

  -- function_properties differential {X Y} [Vec X] [Vec Y] (f : X→Y) : X → X → Y
  -- argument f
  --   isLin := by admit,
  --   isSmooth, diff_simp

  -- namespace tests

  --   variable {X Y Z} [Vec X] [Vec Y] [Vec Z]

  --   example : (∂ λ (f : X⟿Y) => f) = λ f df => df := 
  --   by simp

  --   example : (∂ λ (f : X⟿Y) x => f x) = λ f df x => df x := 
  --   by simp

  --   example (r : ℝ) : (∂ λ (f : X⟿Y) => r*f) = λ (f df : X⟿Y) => r*df := 
  --   by simp

  --   example (g : X⟿Y) : (∂ λ (f : X⟿Y) => f + g) = λ f df => df := 
  --   by simp

  --   example : (∂ λ (f : X⟿Y) => ∂ f.1) = λ f df x dx => ∂ df.1 x dx := 
  --   by simp

  --   example : (∂ λ (f : X⟿Y) => ∂ f.1) = λ f df x dx => ∂ df.1 x dx := 
  --   by simp

  -- end tests

  variable {X Y Z ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] [SemiHilbert Z] [SemiHilbert W]


  @[simp] 
  theorem elem_wise_comp_arg (A : X → Y → Z) [IsSmooth A] [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x) (f x))† = λ (f' : X⟿Z) => λ x ⟿ (A x)† (f' x) := sorry

  @[simp] 
  theorem elem_wise_comp_arg.parm1 (A : X → Y → α → Z) (a : α) [IsSmooth λ x y => A x y a] [∀ x, HasAdjoint (λ y => A x y a)] [∀ x, IsSmooth (λ y => A x y a)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x (f x) a))† = λ (f' : X⟿Z) => λ x ⟿ (λ y => A x y a)† (f' x) := sorry

  @[simp] 
  theorem elem_wise_comp_arg' (A : X → Z → W) [IsSmooth A] [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    (F : (X⟿Y) → X → Z) [IsSmooth F] [∀ f, IsSmooth (F f)] [HasAdjoint (λ f => λ x ⟿ F f x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x) (F f x))† = λ (f' : X⟿W) => (λ f => λ x ⟿ F f x)† (λ x ⟿ (A x)† (f' x)) := sorry

  @[simp] 
  theorem elem_wise_comp_arg'.parm1 
    (a : α)
    (A : X → Z → α → W) [IsSmooth λ x z => A x z a] [∀ x, HasAdjoint (λ z => A x z a)] [∀ x, IsSmooth (λ z => A x z a)]
    (F : (X⟿Y) → X → Z) [IsSmooth F] [∀ f, IsSmooth (F f)] [HasAdjoint (λ f => λ x ⟿ F f x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (A x (F f x) a))† = λ (f' : X⟿W) => (λ f => λ x ⟿ F f x)† (λ x ⟿ (λ z => A x z a)† (f' x)) := sorry


  -- @[simp] 
  -- theorem elem_wise_comp_arg'' 
  --   (F : (X⟿Y) → X → Z → W) 
  --   [∀ f, IsSmooth (F f)] [∀ f x, IsSmooth (F f x)] -- [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
  --   (G : (X⟿Y) → X → Z)  
  --   [IsSmooth G] [∀ f, IsSmooth (G f)]              -- [HasAdjoint (λ f => λ x ⟿ G f x)]
  --   : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (F f x (G f x)))† 
  --     = 
  --     let F' := λ x => (λ ((f,z) : (X⟿Y)×Z) => F f x z)†
  --     let G' := (λ f => λ x ⟿ G f x)†
  --     λ f' => 
  --       let f'' := λ x => F' x (f' x)
  --       let r := λ x => G' ⟨λ x' => (f'' x).2, sorry⟩ x + (f'' x).1 x
  --       ⟨r, sorry⟩
  --     -- λ (f' : X⟿W) => (λ f => λ x ⟿ F f x)† (λ x ⟿ (A x)† (f' x)) 
  --   := sorry


  -- -- example (f : X ⟿ Y × Z) : IsSmooth λ x => (f x).fst := by infer_instance
  -- example (f : X ⟿ Y × Z) : (λ x ⟿ (f x).1) = 0 := by admit

  -- instance [Vec X] [Vec Y] [Vec Z] (f : X ⟿ Y×Z) : IsSmooth (λ x => (f x).1) := sorry

  -- @[simp] 
  -- theorem elem_wise_comp_arg'''  [SemiHilbert Z₁] [SemiHilbert Z₂]
  --   (F : X → Z₁ → Z₂ → W) 
  --   [IsSmooth F] [∀ x, IsSmooth (F x)] [∀ x z₁, IsSmooth (F x z₁)]
  --   [IsSmooth λ x => (λ (z₁,z₂) => F x z₁ z₂)†] 
  --   [∀ x, IsSmooth (λ (z₁,z₂) => F x z₁ z₂)†] -- [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
  --   (G₁ : X → (X⟿Y) → Z₁)  
  --   [IsSmooth G₁] [∀ x, IsSmooth (G₁ x)]
  --   (G₂ : X → (X⟿Y) → Z₂)  
  --   [IsSmooth G₂] [∀ x, IsSmooth (G₂ x)]
  --   : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (F x (G₁ x f) (G₂ x f)))† 
  --     = 
  --     let F' := λ x w ⟿ (λ (z₁,z₂) => F x z₁ z₂)† w
  --     let G₁' := (λ f => λ x ⟿ G₁ x f)†
  --     let G₂' := (λ f => λ x ⟿ G₂ x f)†
  --     λ f' => 
  --       let f'' := λ x ⟿ F' x (f' x)
  --       let f₁ := (λ x => (f'' x).1)
  --       let f₂ := (λ x => (f'' x).2)
  --       let f₁' := (λ x ⟿ (f'' x).fst)
  --       G₁' ⟨f₁,sorry⟩ + G₂' ⟨f₂, sorry⟩
  --       -- G₁' f₁ + G₂' f₂

  --     -- λ (f' : X⟿W) => (λ f => λ x ⟿ F f x)† (λ x ⟿ (A x)† (f' x)) 
  --   := sorry




  --- Divergence in the sense of differential forms
  --- (f : X⟿X⊸Y) is a smooth field of Y-valued 1-forms and divergence is then `*d* f` where `*` is Hodge star and `d` is De Rahm differential
  def flat {X} [Hilbert X] (x : X) : X⊸ℝ := λ y ⊸ ⟪x,y⟫

  noncomputable
  def sharp {X} [Hilbert X] (x : X⊸ℝ) : X := inverse flat x

  theorem sharp.by_basis {X} [Enumtype ι] [FinVec X ι] (x : X⊸ℝ) : sharp x = (∑ i, (x.1 (𝔼 i)) * (𝔼 i : X))  := sorry

  noncomputable
  abbrev divergence {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] (f : X⟿X⊸Y) : X⟿Y :=
    λ x ⟿ ∑ i : ι, ∂ f.1 x (𝔼 i) (𝔼 i)

  noncomputable
  abbrev div {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] (f : X⟿X) : X⟿ℝ :=
    divergence (λ x ⟿ λ dx ⊸ ⟪f x, dx⟫)

  @[simp]
  theorem differential.adj_f.adj_simp {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y]
    : (λ (f : X⟿Y) => (λ x ⟿ λ dx ⊸ ∂ f.1 x dx))† 
      = 
      (λ (f' : X ⟿ X ⊸ Y) => λ (x : X) ⟿ - (divergence f' x)) := sorry

  @[simp]
  theorem differential.adj_f.adj_simp' {X Y ι} [Enumtype ι] [FinVec X ι] [SemiHilbert Y] (v : X)
    : (λ (f : X⟿Y) => (λ x ⟿ ∂ f.1 x v))† 
      = 
      (λ (f' : X ⟿ Y) => λ (x : X) ⟿ - ∂ f'.1 x v) := sorry

  -- set_option trace.Meta.synthInstance true in
  example (A : X → Y → Z) [IsSmooth A] [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)] (f : X → Z) [IsSmooth f]
    : IsSmooth λ x => (A x)† (f x) := by infer_instance

  -- set_option trace.Meta.Tactic.simp.rewrite true in
  -- set_option trace.Meta.Tactic.simp.discharge true in
  example (r : ℝ) : (λ (f : X ⟿ Y) => λ x ⟿ r * f x)† = λ (f' : X⟿Y) =>  (r * f') := by funext f'; ext x; simp[HMul.hMul] done

  example (r : ℝ) : (λ (f : X→Y) (x : X) => r * f x) = (λ (f : X→Y) => r * f) := by simp; funext f x; simp

  example (g : X⟿ℝ)
    : (λ (f : X⟿Y) => λ x ⟿ g x * f x)† = λ (f' : X⟿Y) => (λ x ⟿ g x * f' x) := by simp

  set_option trace.Meta.Tactic.simp.discharge true in
  example {Y} [Hilbert Y] (g : X⟿Y)
    : (λ (f : X⟿Y) => λ x ⟿ ⟪g x, f x⟫)† = λ (f' : X⟿ℝ) => (λ x ⟿ f' x * g x) := 
  by simp done

  example {Y} [Hilbert Y] (A : X⊸Y) : IsSmooth (λ B => ⟪A,B⟫) := by infer_instance

  -- example : ∂ (λ x ⟿ (f' x * g x)).1
  @[simp]
  theorem lin_map_add {X Y} [Vec X] [Vec Y] (A B : X ⊸ Y) (x : X) 
    : (A + B) x = A x + B x := by simp[HAdd.hAdd,Add.add] done

  @[simp]
  theorem lin_map_smul {X Y} [Vec X] [Vec Y] (A : X ⊸ Y) (r : ℝ) (x : X) 
    : (r * A) x = r * A x := by simp[HMul.hMul] done

  @[simp]
  theorem LinMap.mk.eval  {X Y} [Vec X] [Vec Y] (f : X → Y) [IsLin f] (x : X) 
    : PSigma.fst (LinMap.mk f) x = f x := sorry

  @[simp]
  theorem lin_map_diff_apply {X Y Z} [Vec X] [Vec Y] [Vec Z] 
    (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)] (x dx : X) (y : Y)
    : ∂ (λ x => λ y ⊸ f x y) x dx y = ∂ (λ x => f x y) x dx := sorry

  -- @[simp]
  -- theorem lin_map_adj_apply {X Y Z} [Vec X] [Vec Y] [Vec Z] 
  --   (f : X → Y → Z) [IsSmooth f] [∀ x, IsLin (f x)] (x dx : X) (y : Y)
  --   : ∂ (λ x => λ y ⊸ f x y) x dx y = ∂ (λ x => f x y) x dx := sorry


  -- set_option trace.Meta.Tactic.simp.discharge true in
  -- set_option trace.Meta.synthInstance true in
  example {Y} [Hilbert Y] (g : X⟿X⊸Y)
    : (λ (f : X⟿Y) => λ x ⟿ ⟪g x, λ dx ⊸ ∂ f.1 x dx⟫)† 
      =
      λ f' => λ (x : X) ⟿ - (∑ (i : ι), (∂ (λ x ⟿ (f' x * g x)).1 x (𝔼 i)) (𝔼 i)) := 
  by 
    simp; done

  set_option trace.Meta.Tactic.simp.rewrite true in
  example {Y} [Hilbert Y] (g : X⟿Y)
    : (λ (f : X⟿Y) => λ x ⟿ ⟪λ dx ⊸ ∂ g.1 x dx, λ dx ⊸ ∂ f.1 x dx⟫)† 
      = 
      λ f' => λ x ⟿ - ∑ i, ((∂ (f'.1) x (𝔼 i) : ℝ) * (∂ g.1 x (𝔼 i)) + 
                              f' x * ∂ (∂ g.1) x (𝔼 i) (𝔼 i))
      :=
  by 
    simp; done


/-
(fun f' =>
      SmoothMap.mk fun x =>
        -sum fun i =>
            differential (fun x => PSigma.fst f' x) x (Basis.basis i) * differential g.fst x (Basis.basis i) +
              PSigma.fst f' x * differential (fun x => differential g.fst x) x (Basis.basis i) (Basis.basis i)) =
-/

  -- if there is not other option ....
  local instance (priority := low-10) (f : X → Y) [IsLin f] : IsSmooth f := linear_is_smooth f
  local instance (priority := low-10) (f : X → Y) [HasAdjoint f] : IsLin f := sorry
  local instance (priority := low-10) (f : X → Y) [inst : HasAdjDiff f] : IsSmooth f := inst.1
  local instance (priority := low-10) (f : X → Y) [inst : HasAdjDiff f] : ∀ x, HasAdjoint (∂ f x) := inst.2

  set_option trace.Meta.Tactic.simp.discharge true in
  example (L : X → ℝ) (x : ℝ ⟿ X) [hL : HasAdjDiff L]
    : (∂† λ (x : ℝ ⟿ X) => λ (t : ℝ) ⟿ L (x t))
      =
      0
    :=
  by
    simp[adjDiff]
    done

  -- set_option synthInstance.maxHeartbeats 30000

  example (F : X → (X⟿Y) → Z → W) 
    [IsSmooth F] [∀ x f, IsSmooth (F x f)] -- [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    [∀ x, HasAdjoint (λ ((f,z) : (X⟿Y)×Z) => F x f z)]
    (f : X ⟿ Y)
    : IsSmooth (λ (x : X) => (λ (fz : (X⟿Y)×Z) => F x fz.1 fz.2)†) := by infer_instance

  -- @[simp]
  theorem hoho
    (F : X → (X⟿Y) → Z → W) 
    [IsSmooth F] [∀ x f, IsSmooth (F x f)] -- [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    [∀ x, HasAdjoint (λ (fz : (X⟿Y)×Z) => F x fz.1 fz.2)]
    (G : X → (X⟿Y) → Z)  
    [IsSmooth G] [∀ f, IsSmooth (G f)]
    [HasAdjoint (λ f => λ x ⟿ G x f)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (F x f (G x f)))† 
      = 
      let F' := λ x w ⟿ (λ (fz : (X⟿Y)×Z) => F x fz.1 fz.2)† w
      let G' := (λ f => λ x ⟿ G x f)†
      λ f' => 
        let Ff' := λ x ⟿ F' x (f' x)
        let a := G' (λ x ⟿ (Ff' x).2)
        let b := λ x ⟿ (Ff' x).1 x
        λ x ⟿ a x + b x 
    := sorry

  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjoint f := sorry
  instance {X Y} [Vec X] [Vec Y] (f : X → Y) : IsSmooth f := sorry


  set_option trace.Meta.Tactic.simp.discharge true in
  theorem hoho'
    (F : X → (X⟿Y) → Z → W) 
    [IsSmooth F] [∀ x f, IsSmooth (F x f)] -- [∀ x, HasAdjoint (A x)] [∀ x, IsSmooth (A x)]
    [∀ x, HasAdjoint (λ (fz : (X⟿Y)×Z) => F x fz.1 fz.2)]
    [IsSmooth fun x => fun w ⟿ adjoint (λ (fz : (X⟿Y)×Z) => F x fz.1 fz.2) w]
    (G : X → (X⟿Y) → Z)  
    [IsSmooth G] [∀ f, IsSmooth (G f)]
    [HasAdjoint (λ f => λ x ⟿ G x f)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (F x f (G x f)))† 
      = 
      let F' := λ x w ⟿ (λ (fz : (X⟿Y)×Z) => F x fz.1 fz.2)† w
      let G' := (λ f => λ x ⟿ G x f)†
      λ f' => 
        let Ff' := λ x ⟿ F' x (f' x)
        let a := G' (λ x ⟿ (Ff' x).2)
        let b := λ x ⟿ (Ff' x).1 x
        λ x ⟿ a x + b x 
    := 
  by
    simp
    -- rw[hoho]



  theorem hihi  [SemiHilbert Z₁] [SemiHilbert Z₂]
    (F : X → Z₁ → Z₂ → W) 
    [IsSmooth F] [∀ x, IsSmooth (F x)] [∀ x z₁, IsSmooth (F x z₁)]
    (G₁ : X → (X⟿Y) → Z₁)  
    [IsSmooth G₁] [∀ x, IsSmooth (G₁ x)]
    (G₂ : X → (X⟿Y) → Z₂)  
    [IsSmooth G₂] [∀ x, IsSmooth (G₂ x)]
    : (λ (f : X ⟿ Y) => λ (x : X) ⟿ (F x (G₁ x f) (G₂ x f)))† 
      = 0
    := sorry


  -- set_option synthInstance.maxHeartbeats 500000

  -- instance : IsSmooth 




  -- 
  -- instance diff.arg_y.isSmooth' (f : X → Y → Z) [IsSmooth f] [∀ x, IsSmooth (f x)] (x dx) : IsSmooth (λ x => ∂ f x dx) := sorry

  -- set_option trace.Meta.synthInstance true in
  example (L : X → X → ℝ) (x : ℝ ⟿ X) [IsSmooth L] [∀ y, HasAdjDiff (λ x => L x y)] [∀ x, HasAdjDiff (L x)]
    : IsSmooth fun (a : ℝ) (dx : ℝ⟿X) => differential (L (PSigma.fst x a)) (PSigma.fst x a) (PSigma.fst dx a) := 
    -- : IsSmooth fun (a : ℝ) => differential (L (PSigma.fst x a)) := 
  by 
    infer_instance

  instance {X Y} [SemiHilbert X] [SemiHilbert Y] (f : X → Y) : HasAdjoint f := sorry

  set_option trace.Meta.Tactic.simp.rewrite true in
  example (L : X → X → ℝ) (x : ℝ ⟿ X) [IsSmooth L] [∀ y, HasAdjDiff (λ x => L x y)] [∀ x, HasAdjDiff (L x)]
    : (∂† λ (x : ℝ ⟿ X) => λ (t : ℝ) ⟿ L (x t) (x t))
      =
      0
    :=
  by
    simp[adjDiff]
    funext x
    rw[hoho]
    -- simp (config := {zeta := true}) only [SmoothMap.mk.eval]
    -- simp only []
    -- simp (config := {singlePass := true}) only [SmoothMap.mk.eval]
    -- simp (config := {singlePass := true}) only [SmoothMap.mk.eval]
    -- simp (config := {singlePass := true}) only [SmoothMap.mk.eval]
    -- simp (config := {singlePass := true}) only [SmoothMap.mk.eval]
    -- simp (config := {singlePass := true}) only [SmoothMap.mk.eval]
    -- simp (config := {singlePass := true}) only [SmoothMap.mk.eval]

    -- simp (config := {singlePass := true})
    -- simp (config := {singlePass := true})
    -- simp (config := {singlePass := true})
    -- simp (config := {singlePass := true})
    -- simp (config := {singlePass := true})
    -- simp (config := {singlePass := true})
    -- simp (config := {singlePass := true})
    done

/-
  

  set_option trace.Meta.Tactic.simp.discharge true in
  example (L : X → X → ℝ) [IsSmooth L] [∀ x, IsSmooth (L x)] (x : ℝ ⟿ X)
    : ((∂ λ (x : ℝ ⟿ X) => λ (t : ℝ) ⟿ L (x t) (∂ x.1 t 1)) x)†
      =
      0
    :=
  by
    simp
    done

-- (fun f' =>
--       SmoothMap.mk fun x =>
--         -sum fun i =>
--             PSigma.fst (differential (SmoothMap.mk fun x => PSigma.fst f' x * PSigma.fst g x).fst x (Basis.basis i))
--               (Basis.basis i)) 

/-
v  @[simp]
  theorem diff_adj' (v : X)
    : ∂ (λ (f : ℝ⟿ℝ) => integral (λ x ⟿ (∂ f.1 x 1)*(∂ f.1 x 1))) 
      = 
      λ f df => integral (λ x ⟿ ((∂ df.1 x (1:ℝ))*(∂ f.1 x 1) + (∂ f.1 x 1)*(∂ df.1 x 1))) :=  
  by simp

  @[simp]
  theorem asdf (P : (X → Y) → Prop) [Vec ((h : X → Y) ×' P h)] (f g : (h : X → Y) ×' P h) (x : X) : (f + g).1 x = f.1 x + g.1 x := sorry
  @[simp]
  theorem asdf2 (P : (X → Y) → Prop) [Vec ((h : X → Y) ×' P h)] (f g : (h : X → Y) ×' P h) (x : X) : (f - g).1 x = f.1 x + g.1 x := sorry

  example (f g : X⟿Y) (x : X) : (f + g) x = f x + g x := by simp

  @[simp]
  theorem hmul_fun_adj (g : X⟿ℝ) [SemiHilbert (X⟿ℝ)] : (λ (f : X⟿ℝ) => λ x ⟿ g x * f x)† = λ f' => λ x ⟿ g x * f' x := sorry



  @[simp]
  theorem smul_adj_arg (g : X⟿ℝ) [SemiHilbert (X⟿Y)] : (λ (f : X⟿Y) => λ x ⟿ g x * f x)† = λ (f' : X⟿Y) => λ x ⟿ g x * f' x := sorry
  
  @[simp]
  theorem smul_pointwise_adj (g : X⟿ℝ) [SemiHilbert (X⟿Y)] : (λ (f : X⟿Y) => g * f)† = λ (f' : X⟿Y) => g * f' := 
  by
    rw[!?((λ (f : X⟿Y) => g * f) = λ (f : X⟿Y) => λ x ⟿ g x * f x)]
    simp

  instance : SemiInner (X ⟿ Y) := SemiInner.mk sorry sorry sorry sorry
  instance : SemiHilbert (X ⟿ Y) := SemiHilbert.mk sorry sorry sorry sorry sorry sorry

  set_option pp.all true in
  @[simp]
  theorem smul_adj (r : ℝ) : (λ (f : X⟿Y) => r * f)† = λ (f' : X⟿Y) => r * f' := 
  by
    simp

-/


  def integral {X Y ι} [Enumtype ι] [FinVec X ι] [Vec Y] (f : X ⟿ Y) : 𝓓 X → Y := sorry


  instance : IsLin    (λ (f : X ⟿ Y) => integral f) := sorry
  instance : IsSmooth (λ (f : X ⟿ Y) => integral f) := sorry

  @[simp]
  theorem integral.arg_f.diff_simp : ∂ (λ (f : X ⟿ Y) => integral f) = λ f df => integral df := sorry

  @[simp]
  theorem integral_diff_simp 
    : ∂ (λ (f : X⟿Y) => integral f)  = λ f df => integral df := sorry

  example
    : ∂ (λ (f : X⟿Y) => integral ((2:ℝ)*f))  = λ f df => integral ((2:ℝ)*df) := by simp

  example (g : X⟿Y)
    : ∂ (λ (f : X⟿Y) => integral (f + g))  = λ f df => integral (df) := by simp

  example (g : X⟿Y)
    : ∂ (λ (f : X⟿Y) => integral (λ x ⟿ f x + g x))  = λ f df => integral (df) := by simp

  example (g : X⟿ℝ)
    : ∂ (λ (f : X⟿Y) => integral (λ x ⟿ g x * f x))  = λ (f df : X⟿Y) => integral (λ x ⟿ g x * df x) := by simp

  example (g : X⟿ℝ)
    : ∂ (λ (f : X⟿Y) => integral (λ x ⟿ g x * ∂ f.1 x x))  = λ (f df : X⟿Y) => integral (λ x ⟿ g x * ∂ df.1 x x) := by simp

-/
