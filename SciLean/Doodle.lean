-- import SciLean.Core.FunctionTransformations.RevCDeriv
-- import SciLean.Core.Notation.RevCDeriv
-- import SciLean.Core.FloatAsReal
-- import SciLean.Util.Limit

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  {Y₁ : Type} [SemiInnerProductSpace K Y₁]
  {Y₂ : Type} [SemiInnerProductSpace K Y₂]
  {ι : Type} [EnumType ι]
  {κ : Type} [EnumType κ]
  {μ : Type} [EnumType μ]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


set_default_scalar K 


open LimitNotation

instance {K X} [Inv K] [HSMul K X X] : HDiv X K X := ⟨fun x r => r⁻¹ • x⟩

-- set_option trace.Meta.Tactic.simp.unify true
-- set_option trace.Meta.Tactic.simp.discharge true
-- set_option trace.Meta.isDefEq.onFailure true
example 
  : (revCDeriv K fun (x : ι → X) i => x i)
    =
    fun x => (x, fun dx => dx) := 
by
  conv => 
    lhs
    ftrans only


set_option trace.Meta.Tactic.ftrans.step true 
example (f : X → Y) (hf : HasAdjDiff K f)
  : (revCDeriv K fun x (i : ι) => f x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      (fun i => ydf.1, 
       fun dy => ∑ i, ydf.2 (dy i)) := 
by
  conv => 
    lhs
    ftrans only



example (f : X → κ → Y) (hf : ∀ j, HasAdjDiff K (f · j))
  : (revCDeriv K fun x (i : ι) (j : κ) => f x j)
    =
    fun x => 
      let ydf := revCDeriv K f x
      (fun _ => ydf.1, 
       fun dy => ∑ i, ydf.2 (dy i)) := 
by
  conv => 
    lhs
    ftrans only


example (g : ι → Y) (h : ι → X → Y)
  : revCDeriv K (fun (x : X) (i : ι) => let y := 2 • x; g i)
    =
    0 :=
by
  conv => 
    lhs
    ftrans only


def foo (x : K) : K := sorry
def fooD (x dx : K) : K := sorry


@[fprop] 
theorem asdf' (g : X → K) : HasAdjDiff K (fun x => foo (g x)) := sorry

@[ftrans] 
theorem asdf (g : X → K) : revCDeriv K (fun x => foo (g x)) = fun x => let ydg := revCDeriv K g x; (foo ydg.1, fun dz => ydg.2 (fooD ydg.1 dz)) := sorry

example (f : K → K) (hf : HasAdjDiff K f)
  : revCDeriv K (fun (x : ι →  K) (i : ι)=> 
      let x₁ := foo (x i)
      let x₂ := foo x₁
      let x₃ := foo x₂
      let x₄ := foo x₃
      let x₅ := foo x₄
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize
    let_normalize
    let_normalize


example (f : K → ι → K) (hf : ∀ i,  HasAdjDiff K (f · i))
  : revCDeriv K (fun (x : K) (i : ι)=> 
      let x₁ := foo (2 * f x i)
      let x₂ := foo x₁
      let x₃ := foo x₂
      let x₄ := foo x₃
      let x₅ := foo x₄
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize
    let_normalize
    let_normalize



example {K} [RealScalar K]
  : revCDeriv K (fun (x : K) => 
      let x₁ := x * x; 
      let x₂ := x₁ * x₁; 
      let x₃ := x₂ * x₂; 
      let x₄ := x₃ * x₃; 
      let x₅ := x₄ * x₄; 
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize
    let_normalize


example {K} [RealScalar K]
  : revCDeriv K (fun (x : K) => 
      let x₁ := x + x; 
      let x₂ := x₁ + x; 
      let x₃ := x₂ + x; 
      let x₄ := x₃ + x; 
      let x₅ := x₄ + x; 
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize 
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})


example {K} [RealScalar K] (f : K → K) (hf : HasAdjDiff K f)
  : revCDeriv K (fun (x : K) => 
      let x₁ := f x; 
      let x₂ := x₁ * x₁; 
      let x₃ := x₂ * x₁; 
      let x₄ := x₃ * x₁; 
      let x₅ := x₄ * x₁; 
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize 
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})
    



example {K} [RealScalar K]
  : revCDeriv Float (fun (x : Float) => 
      let x₁ := x * x; 
      let x₂ := x₁ * x; 
      let x₃ := x₂ * x; 
      let x₄ := x₃ * x; 
      let x₅ := x₄ * x; 
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet:=true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet:=true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet:=true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet:=true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet:=true})
    simp
    -- simp (config := {zeta:=false})
    -- let_normalize (config := {removeNoFVarLet:=true})
    -- simp (config := {zeta:=false})
    -- let_normalize (config := {removeNoFVarLet:=true})

set_option trace.Meta.Tactic.simp.rewrite true
-- set_option trace.Meta.Tactic.simp.unify true
-- set_option trace.Meta.Tactic.simp.discharge true

example 
  : revCDeriv Float (fun (xy : (Fin 10 → Float)×(Fin 10 → Float)) i => xy.1 i)
    =
    fun xy => 
      (fun i => xy.1 i,
       fun dz => 
         (fun i => dz i, 0)):=
by
  conv => 
    lhs
    ftrans only


example 
  : revCDeriv Float (fun (x : Fin 10 → Float) (i : Fin 10) => i * x i * x i)
    =
    0 :=
by
  conv =>
    lhs
    ftrans only
    let_normalize (config := {removeFVarProjLet := false})
    simp (config := {zeta := false})
    let_normalize (config := {removeFVarProjLet := false})
    simp (config := {zeta := false})
    let_normalize (config := {removeFVarProjLet := false})
    simp (config := {zeta := false})

    -- ftrans only
  sorry_proof

set_option trace.Meta.Tactic.simp.rewrite true
example 
  : revCDeriv Float (fun (x : ι → Float) (i : ι) => 
      let x₁ := x i;
      let x₂ := x₁ * x₁
      let x₃ := x₂ * x₂
      x₃)
    =
    0 :=
by
  conv =>
    lhs
    ftrans
    let_normalize
    let_normalize


set_option trace.Meta.Tactic.simp.rewrite true
example 
  : revCDeriv K (fun (x : ι → X) (i : ι) => 
      let x₁ := x i;
      let x₂ := x₁ + x₁
      let x₃ := x₂ + x₂
      let x₄ := x₃ + x₃
      let x₅ := x₄ + x₄
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans only
    let_normalize
    let_normalize



set_option trace.Meta.Tactic.simp.rewrite true
example 
  : revCDeriv K (fun (x : ι → X) (i : ι) => 
      let x₁ := x i + x i;
      let x₂ := x₁ + x₁; 
      let x₃ := x₂ + x₂; 
      let x₄ := x₃ + x₃; 
      let x₅ := x₄ + x₄; 
      x₅)
    =
    0 :=
by
  conv =>
    lhs
    ftrans only
    let_normalize
    let_normalize (config := {removeNoFVarLet := true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet := true})
    let_normalize

set_option trace.Meta.Tactic.simp.rewrite true
example 
  : revCDeriv K (fun (x : ι → X) (i : ι) => 
      let x₁ := x i + x i;
      let x₂ := x₁ + x i; 
      let x₃ := x₂ + x i; 
      x₃)
    =
    0 :=
by
  conv =>
    lhs
    ftrans only
    let_normalize
    let_normalize (config := {removeNoFVarLet := true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet := true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet := true})
    simp (config := {zeta:=false})
    let_normalize (config := {removeNoFVarLet := true})

#exit


set_option trace.Meta.Tactic.simp.rewrite true
example (g : ι → Y) (h : ι → X → Y)
  : revCDeriv K (fun (x : ι → X) (i : ι) => let a := x i; let b := x i; x i + a + b)
    =
    0 :=
by
  conv =>
    lhs
    ftrans only
    ftrans only
    let_normalize
    let_normalize
    let_normalize

#exit

set_option trace.Meta.Tactic.ftrans.step true 
set_option trace.Meta.Tactic.ftrans.rewrite true 
example (f : X → ι → κ → μ → Y) (hf : ∀ i j k, HasAdjDiff K (f · i j k))
  : (revCDeriv K fun x (i : ι) (j : κ) (k : μ)=> f x i j k)
    =
    fun x =>
    let ydf := <∂ (fun x ij => f x ij.fst.fst ij.fst.snd ij.snd) x;
    (fun i j k => Prod.fst ydf ((i, j), k), 
     fun dy => Prod.snd ydf fun I => dy I.fst.fst I.fst.snd I.snd) :=
by
  conv => 
    lhs
    ftrans only
    let_normalize
    let_normalize


set_option trace.Meta.Tactic.simp.rewrite true in
example (f : X → ι → κ → μ → Y) (hf : ∀ i j k, HasAdjDiff K (f · i j k)) (foo : κ → κ) (j' : κ)
  : (revCDeriv K fun x (i : ι) (k : μ)=> let j := foo j'; let x' := x + x; f (x + x') i j k)
    =
    0 := 
    -- fun x =>
    -- let ydf := <∂ (fun x ij => f x ij.fst.fst ij.fst.snd ij.snd) x;
    -- (fun i j k => Prod.fst ydf ((i, j), k), 
    --  fun dy => Prod.snd ydf fun I => dy I.fst.fst I.fst.snd I.snd) :=
by
  conv => 
    lhs
    ftrans only
    let_normalize
    let_normalize
    let_normalize




open Lean Meta Qq in
#eval show MetaM Unit from do

  let e := (Expr.bvar 2).app (.bvar 0)

  let e := q(fun x : Nat => let y := 1+1; fun z => x + y + z)

  let .lam xName xType (.letE yName yType yValue body _) xBi := e
    | return ()

  IO.println (← ppExpr body)
  IO.println ""

  IO.println "bvars"
  body.forEach (fun x => 
    match x with
    | .bvar i => IO.println i
    | _ => pure ())
  IO.println ""

  
  let e' := Expr.letE yName yType yValue (.lam xName xType (body.mapLooseBVarIds #[1,0].get? 0) xBi) false

  IO.println (← ppExpr e)
  IO.println ""
  IO.println (← ppExpr e')
  
  if ¬(← isDefEq e e') then
    throwError "fucked up"


#check Array.get?
