import SciLean.FTrans.FwdDeriv.Basic

open SciLean

variable
  {K : Type _} [NontriviallyNormedField K]
  {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
  {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace K (E j)]

example : fwdDeriv K (fun x : X => x) = fun x dx => (x,dx) := by ftrans

example (x : X) 
  : fwdDeriv K (fun _ : Y => x) = fun y dy => (x, 0) := by ftrans

example (i : ι) 
  : fwdDeriv K (fun (x : (i : ι) → E i) => x i) = fun x dx => (x i, dx i) := by ftrans only

example
  (f : Y → Z) (g : X → Y) 
  (hf : Differentiable K f) (hg : Differentiable K g)
  : fwdDeriv K (fun x : X => f (g x)) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K f ydy.1 ydy.2 
      zdz := by ftrans

example
  (f : X → Y → Z) (g : X → Y)
  (hf : Differentiable K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : Differentiable K g)
  : fwdDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by ftrans

example
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (fwdDeriv K fun (x : X) (i : ι) => f x i)
    = 
    fun x dx =>
      (fun i => f x i, fun i => (fwdDeriv K (f · i) x dx).2) := by ftrans

example
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K f (g x)) (hg : DifferentiableAt K g x)
  : fwdDeriv K (fun x : X => f (g x)) x
    = 
    fun dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K f ydy.1 ydy.2 
      zdz := by ftrans

example
  (f : X → Y → Z) (g : X → Y) (x : X)  
  (hf : DifferentiableAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x)) (hg : DifferentiableAt K g x)
  : fwdDeriv K (fun x : X => let y := g x; f x y) x
    = 
    fun dx => 
      let ydy := fwdDeriv K g x dx 
      let zdz := fwdDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydy.1) (dx,ydy.2)
      zdz := by ftrans

example
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : (fwdDeriv K fun (x : X) (i : ι) => f x i) x
    =
    fun dx =>
      (fun i => f x i, fun i => (fwdDeriv K (f · i) x dx).2) := by ftrans

example
  : fwdDeriv K (fun x : K => x + x + x + x + x)
    =
    fun x dx => 
     (x + x + x + x + x, dx + dx + dx + dx + dx):= 
by
  conv =>
    lhs
    ftrans only
    enter [x,dx]
    simp (config := { zeta := false}) only [Prod.add_def]

#exit  

example
  : fwdDeriv K (fun x : K => x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x)
    =
    fun x dx => 
     (x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x, 
      dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx + dx):= 
by
  ftrans
