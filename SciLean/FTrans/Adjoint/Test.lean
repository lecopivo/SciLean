import SciLean.FTrans.Adjoint.Basic

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  {Z : Type _} [NormedAddCommGroup Z] [InnerProductSpace K Z] [CompleteSpace Z]
  {Y₁ : Type _} [NormedAddCommGroup Y₁] [InnerProductSpace K Y₁] [CompleteSpace Y₁]
  {Y₂ : Type _} [NormedAddCommGroup Y₂] [InnerProductSpace K Y₂] [CompleteSpace Y₂]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace K (E i)] [∀ i, CompleteSpace (E i)]

open SciLean

example
  : (fun (x : X) =>L[K] x)† = fun x =>L[K] x := by ftrans

example
  : (fun (x : X) =>L[K] (0 : Y))† = fun x =>L[K] 0 := by ftrans


set_option trace.Meta.Tactic.ftrans.step true in
example [DecidableEq ι] (i : ι) 
  : (fun (f : PiLp 2 (fun _ => X)) =>L[K] f i)†
    = 
    fun x =>L[K] (fun j => if h : i=j then x else (0 : X))
  := by ftrans


example
  (f : X → Y) (g : X → Z) 
  (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : ((fun x =>L[K] (f x, g x)) : X →L[K] Y×₂Z)†
    =
    fun yz : Y×₂Z =>L[K]
      let x₁ := (fun x =>L[K] f x)† yz.1
      let x₂ := (fun x =>L[K] g x)† yz.2
      x₁ + x₂ := by ftrans


example
  (f : Y → Z) (g : X → Y) 
  (hf : IsContinuousLinearMap K f) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] f (g x))†
    =
    fun z =>L[K]
      let y := (fun y =>L[K] f y)† z
      let x := (fun x =>L[K] g x)† y
      x := by ftrans



example
  (f : X → Y → Z) (g : X → Y)      
  (hf : IsContinuousLinearMap K (fun xy : X×Y => f xy.1 xy.2)) (hg : IsContinuousLinearMap K g)
  : (fun x =>L[K] let y := g x; f x y)†
    =
    fun z =>L[K]
      let xy := ((fun xy : X×₂Y =>L[K] f xy.1 xy.2)†) z
      let x' := ((fun x =>L[K] g x)†) xy.2
      xy.1 + x' := by ftrans

open BigOperators in
example
  (f : X → (i : ι) → E i) (hf : ∀ i, IsContinuousLinearMap K (f · i))
  : ((fun (x : X) =>L[K] fun (i : ι) => f x i) : X →L[K] PiLp 2 E)†
    = 
    (fun x' =>L[K] ∑ i, (fun x =>L[K] f x i)† (x' i))
  := by ftrans


-- instance introducing diamond!!!
@[reducible]
noncomputable
instance instNormedAddCommGroupProdL2
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y]
  : NormedAddCommGroup (X × Y) := by rw[show (X×Y) = (ProdLp 2 X Y) by rfl]; infer_instance

@[reducible]
noncomputable
instance instInnerProductSpaceProdL2
  {K : Type _} [IsROrC K]
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y]
  : @InnerProductSpace K (X × Y) _ (@instNormedAddCommGroupProdL2 K _ X _ _ Y _ _) := 
 show InnerProductSpace K (ProdLp 2 X Y) by infer_instance



-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.ftrans.discharge true in
-- set_option trace.Meta.Tactic.ftrans.step true in
-- set_option trace.Meta.Tactic.simp.unify true in
-- set_option trace.Meta.Tactic.simp.discharge true in

set_option profiler true

example
  (f : Y₁ → Y₂ → Z) (g₁ : X → Y₁) (g₂ : X → Y₂) (h : Y₁ → Y₁)
  (hf : IsContinuousLinearMap K (fun yy : Y₁×Y₂ => f yy.1 yy.2)) 
  (hg₁ : IsContinuousLinearMap K g₁)
  (hg₂ : IsContinuousLinearMap K g₂)
  (hh : IsContinuousLinearMap K h)
  : (fun x =>L[K] f (h (g₁ x)) (g₂ x))†
    =
    0
  :=
by
  ftrans only





instance   
  {X : Type _} [NormedAddCommGroup X] [InnerProductSpace K X] [CompleteSpace X]
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  : InnerProductSpace K (X × Y) := by rw[show (X×Y) = (ProdLp 2 X Y) by rfl];


