import SciLean.Tactic.DataSynth.Attr
import SciLean.Tactic.DataSynth.Elab
import SciLean.Util.RewriteBy
import SciLean.Analysis.Scalar
import SciLean.Tactic.CompiledTactics
import SciLean.Tactic.LSimp.Elab

@[data_synth out f' in f]
def HasDerivAt {X Y: Type} (f : X → Y) (f' : X → X → Y) (x : X) : Prop := sorry

@[data_synth]
theorem id_rule {X} (x : X): HasDerivAt (fun x : X => x) (fun x dx => dx) x := sorry

@[data_synth]
theorem const_rule {X} [Zero X] (x' : X) (x : X): HasDerivAt (fun x : X => x') (fun x dx => 0) x := sorry

--@[data_synth]
theorem comp_rule {X Y Z}
  (f : Y → Z) (g : X → Y) (x : X) (f' g')
  (hf : HasDerivAt f f' (g x)) (hg : HasDerivAt g g' x) :
  HasDerivAt (fun x => f (g x)) (fun x dx => f' (g x) (g' x dx)) x := sorry

--@[data_synth]
theorem let_rule {X Y Z}
  (f : X → Y → Z) (g : X → Y) (x : X) (f' g')
  (hf : HasDerivAt ↿f f' (x, g x)) (hg : HasDerivAt g g' x) :
  HasDerivAt (fun x => f x (g x)) (fun x dx => f' (x, g x) (dx, g' x dx)) x := sorry

@[data_synth]
theorem add_rule {X Y} [Add Y]
  (f g : X → Y) (x : X) (f' g') (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
  HasDerivAt (fun x => f x + g x) (fun x dx => f' x dx + g' x dx) x := sorry

@[data_synth]
theorem sub_rule {X Y} [Sub Y]
  (f g : X → Y) (x : X) (f' g') (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
  HasDerivAt (fun x => f x - g x) (fun x dx => f' x dx - g' x dx) x := sorry

@[data_synth]
theorem mul_rule {X Y} [Add Y] [Mul Y]
  (f g : X → Y) (x : X) (f' g') (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
  HasDerivAt (fun x => f x * g x)
    (fun x dx =>
      let y := f x
      let dy := f' x dx
      let z := g x
      let dz := g' x dx
      dy * z + y * dz) x := sorry



variable (x' : Nat)
set_option trace.Meta.Tactic.data_synth true in
#check (HasDerivAt (fun x : Nat => x'*x*x*x) ?f' 0) rewrite_by data_synth


@[data_synth out f' in f]
def HasFwdDerivAt {X Y: Type} (f : X → Y) (f' : X → X → Y×Y) (x : X) : Prop := sorry

namespace HasFwdDerivAt
@[data_synth]
theorem id_rule {X} (x : X): HasFwdDerivAt (fun x : X => x) (fun x dx => (x,dx)) x := sorry

@[data_synth]
theorem const_rule {X} [Zero X] (x' : X) (x : X): HasFwdDerivAt (fun x : X => x') (fun x dx => (x,0)) x := sorry

--@[data_synth]
theorem comp_rule {X Y Z}
  (f : Y → Z) (g : X → Y) (x : X) (f' g')
  (hf : HasFwdDerivAt f f' (g x)) (hg : HasFwdDerivAt g g' x) :
  HasFwdDerivAt (fun x => f (g x))
    (fun x dx =>
      let ydy := g' x dx
      let y := ydy.1; let dy := ydy.2
      f' y dy) x := sorry


--- We need to have `hg` before `hf` otherwise unification can't figure out what `x` is
theorem let_rule {X Y Z}
  (g : X → Y) (f : Y → X → Z) {x : X} {g' f'}
  (hg : HasFwdDerivAt g g' x) (hf : HasFwdDerivAt (fun yx : Y×X => f yx.1 yx.2) f' (g x,x)) :
  HasFwdDerivAt (fun x => let y := g x; f y x)
    (fun x dx =>
      let ydy := g' x dx
      let y := ydy.1; let dy := ydy.2
      f' (y,x) (dy,dx)) x := sorry

--@[data_synth]

@[data_synth]
theorem add_rule {X Y} [Add Y]
  (f g : X → Y) (x : X) (f' g') (hf : HasFwdDerivAt f f' x) (hg : HasFwdDerivAt g g' x) :
  HasFwdDerivAt (fun x => f x + g x) (fun x dx =>
      let ydy := f' x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := g' x dx
      let z := zdz.1; let dz := zdz.2
      (y + z, dy + dz)) x := sorry

@[data_synth]
theorem sub_rule {X Y} [Sub Y]
  (f g : X → Y) (x : X) (f' g') (hf : HasFwdDerivAt f f' x) (hg : HasFwdDerivAt g g' x) :
  HasFwdDerivAt (fun x => f x - g x) (fun x dx => f' x dx - g' x dx) x := sorry

@[data_synth]
theorem mul_rule {X Y} [Add Y] [Mul Y]
  (f g : X → Y) (x : X) (f' g') (hf : HasFwdDerivAt f f' x) (hg : HasFwdDerivAt g g' x) :
  HasFwdDerivAt (fun x => f x * g x)
    (fun x dx =>
      let ydy := f' x dx
      let y := ydy.1; let dy := ydy.2
      let zdz := g' x dx
      let z := zdz.1; let dz := zdz.2
      (y * z, dy * z + y * dz)) x := sorry
      -- let ydy := f' x dx
      -- let zdz := g' x dx
      -- (ydy.1 * zdz.1, ydy.2 * zdz.1 + ydy.1 * zdz.2)) x := sorry

@[data_synth]
theorem fst_rule {X Y}
  (f : X → Y×Z) (x : X) (f') (hf : HasFwdDerivAt f f' x) :
  HasFwdDerivAt (fun x => (f x).1)
    (fun x dx =>
      let ydy := f' x dx
      (ydy.1.1 , ydy.2.1)) x := sorry

@[data_synth]
theorem snd_rule {X Y}
  (f : X → Y×Z) (x : X) (f') (hf : HasFwdDerivAt f f' x) :
  HasFwdDerivAt (fun x => (f x).2)
    (fun x dx =>
      let ydy := f' x dx
      (ydy.1.2 , ydy.2.2)) x := sorry

variable (x' : Nat)

set_option trace.Meta.Tactic.data_synth true in
#check (HasFwdDerivAt (fun x : Nat×Nat => x) ?f' 0) rewrite_by
              data_synth



set_option trace.Meta.Tactic.data_synth true in
#check (HasFwdDerivAt (fun x : Nat =>
            x*x*x*x*x*x) ?f' 0) rewrite_by
              data_synth


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasFwdDerivAt (fun x : Nat =>
            let y := (x+x)*(x+x)
            x * y) ?f' 0) rewrite_by
              data_synth


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasFwdDerivAt (fun x : Nat =>
            let x₁ := x*x
            let x₂ := x₁*x₁
            let x₃ := x₂*x₂
            let x₄ := x₃*x₃
            x₄) ?f' 0) rewrite_by
              data_synth


set_option trace.Meta.Tactic.data_synth true in
set_option trace.Meta.Tactic.data_synth.normalize true in
set_option trace.Meta.Tactic.data_synth.input true in
#check (HasFwdDerivAt (fun x : Nat =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            let x₄ := x*x₁*x₂*x₃
            x*x₁*x₂*x₃*x₄) ?f' 0) rewrite_by
              data_synth


-- set_option trace.Meta.Tactic.data_synth true in
-- set_option trace.Meta.Tactic.data_synth.normalize true in
-- set_option trace.Meta.Tactic.data_synth.input true in
set_option profiler true in
#check (HasFwdDerivAt (fun x : Nat =>
            let x₁ := x*x
            let x₂ := x*x₁
            let x₃ := x*x₁*x₂
            let x₄ := x*x₁*x₂*x₃
            let x₅ := x*x₁*x₂*x₃*x₄
            let x₆ := x*x₁*x₂*x₃*x₄*x₅
            x*x₁*x₂*x₃*x₄*x₅*x₆) ?f' 0) rewrite_by
              data_synth -normalizeLet +normalizeCore
              -- data_synth


open Lean Meta Elab Qq
#eval show TermElabM Unit from do

  let mut counts : Array Float := #[]
  let mut times : Array Float := #[]
  let N := 11
  for i in [1:N] do
    let n := 10*i + 2

    let f ← withLocalDeclD `x q(Nat) fun x => do
      mkLambdaFVars #[x] (← mkAppFoldlM ``HMul.hMul (Array.mkArray n x))
    let f' ← mkFreshExprMVarQ q(Nat → Nat → Nat×Nat)
    let e ← mkAppM ``HasFwdDerivAt #[f,f',q(0)]

    let start ← IO.monoNanosNow
    let (e',_) ← SciLean.elabConvRewrite e #[] (← `(conv| (data_synth -normalizeLet +normalizeCore)))
    let stop ← IO.monoNanosNow
    let time := (stop - start).toFloat/1e6
    times := times.push time
    counts := counts.push n.toFloat
    IO.println s!"n={n}, time: {time}ms  | {hash e'}"


  let x := counts.map (·.log)
  let y := times.map (·.log)

  let N := x.size
  let dom := N.toFloat * (∑ i, (x.get i)^2) - (∑ i, x.get i)^2
  let nom := (N.toFloat * (∑ i, (x.get i)*y.get! i) - (∑ i, x.get i)*(∑ i, y.get i))
  let slope := nom / dom

  IO.println s!"scaling {slope}"
