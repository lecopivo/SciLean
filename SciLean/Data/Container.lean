import SciLean.Algebra
import SciLean.Std.Enumtype

namespace SciLean

--- Container `C` with index set `ι` and element type `α`
class Cont (C : Type u) (ι : Type v) (α : Type w) where
  toFun : C → ι → α

--- Automatically infering T and dims based on A
class ContData (C : Type u) where
  indexOf : Type v
  valueOf : Type w

-- Is this good idea?
@[reducible] 
instance (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] : ContData C := ⟨ι, α⟩

attribute [reducible, inline] ContData.indexOf ContData.valueOf

namespace Cont

  -- Function that should be interpreted as a container
  def ContFun (α β) := α → β
  infix:34 " ↦ " => ContFun
  
  def toCont (f : α → β) : α ↦ β := f
  instance (ι : Type v) (α : Type w) : Cont (ι ↦ α) ι α := ⟨λ f => f⟩
  -- TODO: support `cont (i,j) => f i j`
  macro "cont" xs:Lean.explicitBinders "=> " b:term : term => Lean.expandExplicitBinders `Cont.toCont xs b

  export ContData (indexOf valueOf)

  -- Maybe not a good idea
  -- instance (ι : Type v) (α : Type w) : Cont (ι → α) ι α := ⟨λ f => f⟩

  @[reducible]
  abbrev get {C} [ContData C] [Cont C (indexOf C) (valueOf C)] (c : C) := @toFun _ (indexOf C) (valueOf C) _ c

  --- TODO:
  --  Merge all those macros into one
  --
  --  Add slicing notation:
  --      1. f[:]  ==  f[:₀]  ==  cont i => f[i]  : ι ↦ α       
  --      2. f[:,:]  ==  cont (i,j) => f[i,j]  : ι₀ × ι₁ ↦ α 
  --      2. f[:₀,:₁]  ==  cont i j => f[i,j]  : ι₀ ↦ ι₁ ↦ α 
  --      3. f[:₁,:₀]  ==  cont j i => f[i,j]  : ι₁ ↦ ι₀ ↦ α 
  --      4. f[:,:₁,:]  ==  cont (i,j) k => f[i,k,j] : ι₀ × ι₂ ↦ ι₁ ↦ α
  -- 
  --  For indices that are Fintype add ranged notation
  --      1. f[a:b]  == cont i : Range a b => f[(coe (Range a b) ι i)]   : Range a b ↦ α
  --      2. f[a:b,:]  == cont (i,j) : (Range a b) × ι₁ => f[(coe (Range a b) ι i),j]  : (Range a b)×ι₁ ↦ α
  --      3. f[a:b,:₁]  == cont (i,j) : (Range a b) ι₁ => f[(coe (Range a b) ι i),j]  : (Range a b) ↦ ι₁ ↦ α
  macro c:term noWs "[" i1:term"]" : term =>
    `(get $c $i1)

  macro c:term noWs "[" i1:term "," i2:term "]" : term =>
    `(get $c ($i1,$i2))

  macro c:term noWs "[" i1:term "," i2:term "," i3:term "]" : term =>
    `(get $c ($i1,$i2,$i3))

  macro c:term noWs "[" i1:term "," i2:term "," i3:term "," i4:term "]" : term =>
    `(get $c ($i1,$i2,$i3,$i4))

  -- This provides something like Eigen's expression templates
  section HeterogenousArithmetics

     section ElementWise
       variable {ι : Type v}
       variable {C : Type u} {α : Type w} [Cont C ι α]
       variable {C' : Type u'} {α' : Type w'} [Cont C' ι α']

       instance [HAdd α α' β] : HAdd C C' (ι ↦ β) := ⟨λ c c' => λ i => c[i] + c'[i]⟩
       instance [HSub α α' β] : HSub C C' (ι ↦ β) := ⟨λ c c' => λ i => c[i] - c'[i]⟩

     end ElementWise

     section Mul
       variable {ι κ μ : Type v}
       variable {C : Type u} {α : Type w} [Cont C (ι×κ) α]
       variable {C' : Type u'} {α' : Type w'} [Cont C' (κ×μ) α']

       -- Just a prototype because I do not have a `Fintype` defined
       def sum [Add β] : (α → β) → β := sorry

       instance [HMul α α' β] [Add β] : HMul C C' (ι × μ ↦ β) := ⟨λ c c' (i,j) => sum λ k => c[i,k] * c'[k,j]⟩

     end Mul

     section Broadcasting

       variable {ι : Type v}
       variable {C : Type u} {α : Type w} [Cont C ι α]

       instance [HMul α β γ] : HMul C β (ι ↦ γ) := ⟨λ a b i => a[i]*b⟩
       instance [HMul β α γ] : HMul β C (ι ↦ γ) := ⟨λ b a i => b*a[i]⟩
    
     end Broadcasting

  end HeterogenousArithmetics

  section ExtraOperations

     class Intro (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       intro : (indexOf C → valueOf C) → C
       valid : ∀ f i, (intro f)[i] = f i

     export Intro (intro)

     instance {C ι α} [Cont C ι α] [Intro C] : Coe (ι ↦ α) C := ⟨λ f => intro f⟩
  
     class Set (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       set : C → (indexOf C) → (valueOf C) → C
       valid : ∀ c i a, ((set c i a)[i] = a) ∧ 
                        (∀ j, j ≠ i → (set c i a)[j] = c[j])

     export Set (set)

     class MapIdx (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       mapIdx : ((indexOf C) → (valueOf C) → (valueOf C)) → C → C
       valid : ∀ f c i, (mapIdx f c)[i] = f i (c[i])

     export MapIdx (mapIdx)

     class Map (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       map : ((valueOf C) → (valueOf C)) → C → C
       valid : ∀ f c i, (map f c)[i] = f (c[i])

     export Map (map)

     -- map₂ can be done with mapIdx, but with map₂ we can reuse memore more efficiently
     -- Also we do want MapIdx for sparse data structures
     class Map₂ (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       map₂ : ((valueOf C) → (valueOf C) → (valueOf C)) → C → C → C
       valid : ∀ f c d i, (map₂ f c d)[i] = f (c[i]) (d[i])

     export Map₂ (map₂)

     -- Some containers can have infinite(effectively) index set `(indexOf C)` but only finite many indices actually hold a value
     -- Prime example is OpenVDB/NanoVDB but sparse matrices also qualify for this
     class Active (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       active : C → (indexOf C) → Bool
       finite : (c : C) → Enumtype {i : (indexOf C) // active c i = true }

     -- Add ActiveMapIdx -- runs map only over active indices

  end ExtraOperations

  section VectorSpace

     variable {C : Type u} {ι : Type v} {α : Type w}

     instance [ContData C] [Cont C (indexOf C) (valueOf C)] [Vec (valueOf C)] [Intro C] : Vec C :=
     {
       add := λ c d => intro (c + d)
       sub := λ c d => intro (c - d)
       neg := λ c => intro (λ i => -c[i])
       zero := intro (λ _ => 0)
       hMul := λ s c => intro (s * c)
       add_assoc := sorry,
       add_comm := sorry,
       add_zero := sorry,
       zero_add := sorry
     }

  end VectorSpace

end Cont

namespace Cont.Tests

variable (f : Fin 3 × Fin 2 ↦ Nat) (g : Fin 2 × Fin 5 ↦ Nat) (h : Fin 3 × Fin 5 ↦ Nat)
variable (r s : Nat)

#check f[1,0]
#check λ i j => f[i,j]

#check ((λ i => f[i,·] + f[i,·]))
-- #check ((λ i => f[i,:] + f[i,:])) : i → j ↦ Nat

#check f + f
#check r * f * g + s * h
-- #check cont (i,j) => f[j,i]

@[reducible]
abbrev toindexOf : List Nat → Type 
| [] => Unit
| [n] => Fin n
| n :: ns => Fin n × toindexOf ns

def List.product (l : List Nat) : Nat := do
  let a := l.toArray
  let mut prod := 1
  for i in [0:a.size] do
    prod := prod * a[i]
  prod

-- def toLinear : (l : List Nat) → toindexOf l → Nat
-- | [], index => 0
-- | [n], index => 0
-- | (n :: ns), index => (Prod.fst index) * toLinear ns (Prod.snd index)



example : (Fin 3 × Fin 2) = toindexOf [3,2] := by rfl

variable {n m} (F : toindexOf [n,m,n] ↦ Nat) 

#check λ i j k => (F[i,j,k] : Nat)
#check (cont i j k => F[i,j,k])
#check ((3,2,0) : toindexOf [3,2,4])

#check λ i j => (F[i,j,·])

-- structure Kernel where
--   types : Array String
--   funs : Array (String × Fin (types.size) × (Array (Fin types.size)))   --- (name, argument types, output type)
--   nonempty : 0 < types.size

end Cont.Tests


