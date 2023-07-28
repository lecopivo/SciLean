import SciLean.FTrans.FDeriv.Basic
import SciLean.Profile

open SciLean

#profile_this_file

set_option profiler true

variable {K : Type _} [NontriviallyNormedField K]
variable {X : Type _} [NormedAddCommGroup X] [NormedSpace K X]
variable {Y : Type _} [NormedAddCommGroup Y] [NormedSpace K Y]
variable {Z : Type _} [NormedAddCommGroup Z] [NormedSpace K Z]
variable {ι : Type _} [Fintype ι]
variable {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

example
  : (fderiv K fun x : X => x) = fun _ => fun dx =>L[K] dx
  := by ftrans only

example (x : X)
  : (fderiv K fun _ : Y => x) = fun _ => fun dx =>L[K] 0
  := by ftrans only

example
  (x : X)
  (g : X → Y) (hg : DifferentiableAt K g x)
  (f : Y → Z) (hf : DifferentiableAt K f (g x))
  : (fderiv K fun x : X => f (g x)) x
    =
    let y := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K f y dy
      dz :=
by ftrans only  

example
  (g : X → Y) (hg : Differentiable K g)
  (f : Y → Z) (hf : Differentiable K f)
  : (fderiv K fun x : X => f (g x))
    =
    fun x => 
      let y := g x
      fun dx =>L[K]
        let dy := fderiv K g x dx
        let dz := fderiv K f y dy
        dz :=
by 
  ftrans only

example
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : DifferentiableAt K (fun xy : X×Y => f xy.1 xy.2) (x, g x)) 
  (hg : DifferentiableAt K g x)
  : (fderiv K
      fun x : X =>
        let y := g x
        f x y) x
    =
    let y  := g x
    fun dx =>L[K]
      let dy := fderiv K g x dx
      let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
      dz := by ftrans only

example
  (f : X → Y → Z) (g : X → Y) 
  (hf : Differentiable K fun xy : X×Y => f xy.1 xy.2) (hg : Differentiable K g)
  : (fderiv K fun x : X =>
       let y := g x
       f x y)
    =
    fun x => 
      let y  := g x
      fun dx =>L[K]
        let dy := fderiv K g x dx
        let dz := fderiv K (fun xy : X×Y => f xy.1 xy.2) (x,y) (dx, dy)
        dz := by ftrans only

example
  (f : X → (i : ι) → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f · i) x)
  : (fderiv K fun (x : X) (i : ι) => f x i) x
    = 
    fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx
  := by ftrans only

example
  (f : X → (i : ι) → E i) (hf : ∀ i, Differentiable K (f · i))
  : (fderiv K fun (x : X) (i : ι) => f x i)
    = 
    fun x => fun dx =>L[K] fun i =>
      fderiv K (f · i) x dx
  := by ftrans only

example
  (f : (i : ι) → X → E i) (x : X) (hf : ∀ i, DifferentiableAt K (f i) x)
  : (fderiv K fun (x : X) (i : ι) => f i x) x
    = 
    fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := by ftrans only


example
  (f : (i : ι) → X → E i) (hf : ∀ i, Differentiable K (f i))
  : (fderiv K fun (x : X) (i : ι) => f i x)
    = 
    fun x => fun dx =>L[K] fun i =>
      fderiv K (f i) x dx
  := by ftrans only

