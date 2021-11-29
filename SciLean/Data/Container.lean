namespace SciLean

class Fintype (α : Type u) where
  n : Nat
  fromFin : Fin n → α
  toFin : α → Fin n
  to_from : ∀ i, toFin (fromFin i) = i
  from_to : ∀ a, fromFin (toFin a) = a

--- Container `C` with index set `ι` and element type `α`
class Cont (C : Type u) (ι : Type v) (α : Type w) where
  toFun : C → ι → α

--- Automatically infering T and dims based on A
class ContData (C : Type u) where
  indexType : Type v
  valueType : Type w

-- Is this good idea?
@[reducible] 
instance (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] : ContData C := ⟨ι, α⟩

attribute [reducible, inline] ContData.indexType ContData.valueType

namespace Cont

  -- Function that should be interpreted as a container
  def ContFun (α β) := α → β
  infix:34 " ↦ " => ContFun

  def toCont (f : α → β) : α ↦ β := f
  instance (ι : Type v) (α : Type w) : Cont (ι ↦ α) ι α := ⟨λ f => f⟩

  -- Maybe not a good idea
  -- instance (ι : Type v) (α : Type w) : Cont (ι → α) ι α := ⟨λ f => f⟩

  @[reducible]
  abbrev indexOf {C} (c : C) [ContData C] := ContData.indexType C

  @[reducible]
  abbrev valueOf {C} (c : C) [ContData C] := ContData.valueType C

  @[reducible]
  abbrev get {C} [ContData C] [Cont C (ContData.indexType C) (ContData.valueType C)] (c : C) := @toFun _ (indexOf c) (valueOf c) _ c

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

     class Intro (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] where
       intro : (ι → α) → C
       valid : ∀ f i, (intro f)[i] = f i

     export Intro (intro)

     -- instance {C ι α} [Cont C ι α] [Intro C ι α] : Coe (ι ↦ α) C := ⟨λ f => intro f⟩
  
     class Set (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] where
       set : C → ι → α → C
       valid : ∀ c i a, ((set c i a)[i] = a) ∧ 
                        (∀ j, j ≠ i → (set c i a)[j] = c[j])

     export Set (set)

     class MapIdx (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] where
       mapIdx : (ι → α → α) → C → C
       valid : ∀ f c i, (mapIdx f c)[i] = f i (c[i])

     def mapIdx {C : Type u}
         [ContData C] 
         [Cont C (ContData.indexType C) (ContData.valueType C)] 
         [MapIdx C (ContData.indexType C) (ContData.valueType C)]
         (f : (ContData.indexType C) → (ContData.valueType C) → (ContData.valueType C) ) (c : C) : C
         := MapIdx.mapIdx f c

     class Map (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] where
       map : (α → α) → C → C
       valid : ∀ f c i, (map f c)[i] = f (c[i])

     def map {C : Type u}
         [ContData C] 
         [Cont C (ContData.indexType C) (ContData.valueType C)] 
         [Map C (ContData.indexType C) (ContData.valueType C)]
         (f : (ContData.valueType C) → (ContData.valueType C) ) (c : C) : C
         := Map.map (ι := (ContData.indexType C)) f c

     -- map₂ can be done with mapIdx, but with map₂ we can reuse memore more efficiently
     class Map₂ (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] where
       map₂ : (α → α → α) → C → C → C
       valid : ∀ f c d i, (map₂ f c d)[i] = f (c[i]) (d[i])

     def map₂ {C : Type u} [ContData C] 
         [Cont C (ContData.indexType C) (ContData.valueType C)] 
         [Map₂ C (ContData.indexType C) (ContData.valueType C)]
         (f : (ContData.valueType C) → (ContData.valueType C) → (ContData.valueType C)) (c d : C) : C
         := Map₂.map₂ (ι := (ContData.indexType C)) f c d

     -- Some containers can have infinite(effectively) index set `ι` but only finite many indices actually hold a value
     -- Prime example is OpenVDB/NanoVDB but sparse matrices also qualify for this
     class Active (C : Type u) (ι : Type v) (α : Type w) [Cont C ι α] where
       active : C → ι → Bool
       finite : (c : C) → Fintype {i : ι // active c i = true }

  end ExtraOperations

  -- necassary to define vector space
  section HomogenousOperations

     variable {C : Type u} {ι : Type v} {α : Type w}
     variable [Cont C ι α] [Intro C ι α] [Map C ι α] [Map₂ C ι α]

     instance [Add α] : Add C := ⟨λ c d => map₂ (λ x y => x + y) c d⟩
     instance [Sub α] : Sub C := ⟨λ c d => map₂ (λ x y => x - y) c d⟩
     instance [Mul α] : Mul C := ⟨λ c d => map₂ (λ x y => x * y) c d⟩
     instance [Div α] : Div C := ⟨λ c d => map₂ (λ x y => x / y) c d⟩

     instance [HMul α β α] : HMul C β C := ⟨λ c b => map (λ x => x * b) c⟩
     instance [HMul β α α] : HMul β C C := ⟨λ b c => map (λ x => b * x) c⟩

     instance [Neg α] : Neg C := ⟨λ c => map (λ x => -x) c⟩

     -- instance [Zero α] : Zero C := ⟨intro λ _ => 0⟩

  end HomogenousOperations

end Cont


namespace Tests

variable (f : Fin 3 × Fin 2 ↦ Nat) (g : Fin 2 × Fin 5 ↦ Nat) (h : Fin 3 × Fin 5 ↦ Nat)
variable (r s : Nat)

#check f[1,0]
#check λ i j => f[i,j]

#check ((λ i => f[i,·] + f[i,·]))
-- #check ((λ i => f[i,:] + f[i,:])) : i → j ↦ Nat

#check f + f
#check r * f * g + s * h

@[reducible]
abbrev toIndexType : List Nat → Type 
| [] => Unit
| [n] => Fin n
| n :: ns => Fin n × toIndexType ns

def List.product (l : List Nat) : Nat := do
  let a := l.toArray
  let mut prod := 1
  for i in [0:a.size] do
    prod := prod * a[i]
  prod

-- def toLinear : (l : List Nat) → toIndexType l → Nat
-- | [], index => 0
-- | [n], index => 0
-- | (n :: ns), index => (Prod.fst index) * toLinear ns (Prod.snd index)


example : (Fin 3 × Fin 2) = toIndexType [3,2] := by rfl

variable {n m} (F : toIndexType [n,m,n] ↦ Nat) 

#check λ i j k => (F[i,j,k] : Nat)
#check ((3,2,0) : toIndexType [3,2,4])

#check λ i j => (F[i,j,·])

-- structure Kernel where
--   types : Array String
--   funs : Array (String × Fin (types.size) × (Array (Fin types.size)))   --- (name, argument types, output type)
--   nonempty : 0 < types.size

end Tests
