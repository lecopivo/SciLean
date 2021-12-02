import SciLean.Algebra
import SciLean.Std.Enumtype

namespace SciLean

--- Container `C` with index set `ι` and element type `α`
class Cont (C : Type u) (ι : Type v) (α : Type w) where
  toFun : C → ι → α

--- Automatically infering `ι` and `α` based on C
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
  infixr:34 " ↦ " => ContFun
  
  -- Mark function as a container
  abbrev toCont (f : α → β) : α ↦ β := f
  @[simp] theorem toCont_apply (f : α → β) : toCont f = f := by rfl
  instance (ι : Type v) (α : Type w) : Cont (ι ↦ α) ι α := ⟨λ f => f⟩
  instance (ι : Type) (α : Type) [Vec α] : Vec (ι ↦ α) := by simp[ContFun] infer_instance
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
  --  Element assignment:
  --      1. f[i] := x    ==   f := f.set i x
  --      2. f[i] += x    ==   f := f.set i (f[i] + x)
  --
  --  Add slicing notation:
  --      1. f[:]    ==  f[:₀]  ==  cont     i => f[i]    : ι ↦ α       
  --      2. f[:,:]             ==  cont (i,j) => f[i,j]  : ι₀ × ι₁ ↦ α 
  --  Curry notation:  
  --      3. f[:₀,:₁]   ==  cont     i j => f[i,j]   : ι₀ ↦ ι₁ ↦ α       where  f : ι₀ × ι₁ ↦ α 
  --      4. f[:₁,:₀]   ==  cont     j i => f[i,j]   : ι₁ ↦ ι₀ ↦ α       where  f : ι₀ × ι₁ ↦ α 
  --      5. f[:,:₁,:]  ==  cont (i,j) k => f[i,k,j] : ι₀ × ι₂ ↦ ι₁ ↦ α  where  f : ι₀ × ι₁ × ι₂ ↦ α 
  --  Uncurry notation:
  --      5. f[:][:]  == cont (i,j) => f[i][j]  :  ι₀ × ι₁ ↦ α       where  f : ι₀ ↦ ι₁ ↦ α 
  -- 
  --  Common examples:  (mean: ∑' == 1/n * ∑) (norm: ∥ ∥)
  --      1. average of columns:    (∑' j, A[:,j])(A[:₀,:₁] - ∑ j', A[:,j'])[:,:]
  --      2. center columns:         (A[:₀,:₁] - ∑ j', A[:,j'])[:,:]
  --      3. normalize of columns:  ((A[:₁,:₀] / (cont j, ∥A[:,j]∥))[:₁,:₀])[:,:]
  --         The core operation (A[:₁,:₀] / (cont j, ∥A[:,j]∥) produces `B : ι₁ ↦ ι₀ ↦ α`. Uncurrying back to `ι₀ × ι₁ ↦ α` is the awful (`B[:₁,:₀])[:,:]`
  --  
  --  Corner/Odd cases: 
  --        1. curry and uncurry:  (f[:₀,:₁])[:,:]  ==  cont (k,l)     => (cont i j => f[i,j])[k,l]  ==  f
  --        2. not the same as 1:   f[:₀,:₁] [:,:]  ==  cont (i,j,k) l => f[i,l][j,k]                !=  f
  --        3. transpose:          (f[:₁,:₀])[:,:]  ==  cont (k,l)     => (cont j i => f[i,j])[k,l]  ==  transpose f
  --        4. uncurry:             f[:][:]         ==  cont (i,j)     => f[i][j]
  --        5. curry:               f[:₀,:₁]        ==  cont i j       => f[i,j]
  --        6. identity:            f[:]            ==  cont i         => f[i]
  --        7. identity:           (f[:])[:]        ==  cont i         => (cont j => f[j])[i]
  -- 
  --  For indices that are Enumtype add ranged notation  
  --      1. f[a:b]     == cont     i : Fin (dist a b)      => f[offset a i]   : Fin (dist a b) ↦ α
  --      2. f[a:b,:]   == cont (i,j) : Fin (dist a b) × ι₁ => f[offset a i, j]  : Fin (dist a b)×ι₁ ↦ α
  --      3. f[a:b,:₁]  == cont     (i: Fin (dist a b)) j   => f[offset a i, j]  : Fin (dist a b) ↦ ι₁ ↦ α
  --      where (dist a b)   := (toFin b).1 - (toFin a).1
  --            (offset a i) := fromFin (i.1 + (toFin a).1)

  macro c:term noWs "[" i1:term"]" : term =>
    `(get $c $i1)

  macro c:term noWs "[" i1:term "," i2:term "]" : term =>
    `(get $c ($i1,$i2))

  macro c:term noWs "[" i1:term "," i2:term "," i3:term "]" : term =>
    `(get $c ($i1,$i2,$i3))

  macro c:term noWs "[" i1:term "," i2:term "," i3:term "," i4:term "]" : term =>
    `(get $c ($i1,$i2,$i3,$i4))


  section ExtraOperations

     -- Here we use formulation with [ContData C] [Cont C (indexOf C) (valueOf C)]
     -- instead of [Cont C ι α]
     --
     -- This way, for example, `Intro.intro` needs to infer only `C` and does not have to infer `ι` and ‵α`
     -- Plus when declaring instance you can just write, for example, `instance {T} : Intro T`.

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
     -- Edit: On second thought Map₂ is maybe not too important.
     -- class Map₂ (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
     --   map₂ : ((valueOf C) → (valueOf C) → (valueOf C)) → C → C → C
     --   valid : ∀ f c d i, (map₂ f c d)[i] = f (c[i]) (d[i])

     -- export Map₂ (map₂)

     -- Some containers can have infinite(effectively) index set `(indexOf C)` but only finite many indices actually hold a value
     -- Prime example is OpenVDB/NanoVDB but sparse matrices also qualify for this
     class Active (C : Type u) [ContData C] [Cont C (indexOf C) (valueOf C)] where
       active : C → (indexOf C) → Bool
       finite : (c : C) → Enumtype {i : (indexOf C) // active c i = true }

     -- Add ActiveMapIdx -- runs map only over active indices

  end ExtraOperations

  section VectorSpace

     variable {C : Type u} 
     variable [ContData C] [Cont C (indexOf C) (valueOf C)] [Vec (valueOf C)] [Intro C]

     instance instContVecAdd : Add C := ⟨λ c d => intro (λ i => c[i] + d[i])⟩
     instance instContVecSub : Sub C := ⟨λ c d => intro (λ i => c[i] - d[i])⟩
     instance instContVecNeg : Neg C := ⟨λ c => intro (λ i => -c[i])⟩
     instance instContVecHMul : HMul ℝ C C := ⟨λ s c => intro (λ i => s * c[i])⟩
     instance instContVecZero : Zero C := ⟨intro λ _ => 0⟩

     instance contVec [ContData C] [Cont C (indexOf C) (valueOf C)] [Vec (valueOf C)] [Intro C] : Vec C :=
     {
       zero := intro (λ _ => 0)
       add_assoc := sorry,
       add_comm := sorry,
       add_zero := sorry,
       zero_add := sorry
     }

     section VectorOperations

       -- variable {C} [ContData C] [Cont C (indexOf C) (valueOf C)] [Vec (valueOf C)] [Intro C]
       variable {C : Type u} {ι : Type v} {α : Type w} [Cont C ι α] [Intro C] [Vec α]

       
       -- Unfold definition's of vector oprations back
       -- This way we can get fast saxpy type operations i.e.`s*x+y` transforms to `intro λ i => s*x[i] + y[i]`
       -- We specify class instances directly to prevent crazy TC searches.
       @[simp] theorem add_norm (c d : C) : HAdd.hAdd (self := instHAdd) c d = intro (λ i => c[i] + d[i]) := by rfl
       @[simp] theorem sub_norm (c d : C) : HSub.hSub (self := instHSub) c d = intro (λ i => c[i] - d[i]) := by rfl
       @[simp] theorem neg_norm (c : C) : Neg.neg (self := instContVecNeg) c = intro (λ i => -c[i]) := by rfl
       @[simp] theorem hmul_norm (s : ℝ) (c : C) : HMul.hMul (self := instContVecHMul) s c = intro (cont i => s * c[i]) := by rfl
       @[simp] theorem zero_norm : (Zero.zero (self := instContVecZero) : C) = intro (λ _ => 0) := by rfl

       @[simp] theorem get_intro (f : ι ↦ α) : (intro f : C)[i] = f i := by apply Intro.valid; done
       @[simp] theorem get_contFun {i : ι} (f : ι ↦ α) : f[i] = f i := by rfl

       section tests
         abbrev xpy {X} [Vec X] (x y : X) := x + y
         abbrev saxpy {X} [Vec X] (s : ℝ) (x y : X) := s*x + y
         abbrev saxsrypnz {X} [Vec X] (s r : ℝ) (x y z: X) := s*x - r*y + (-z)

         example (x y : C) : xpy x y = intro (λ i => x[i] + y[i]) := by simp done
         example (s : ℝ) (x y : C) : saxpy s x y = intro (λ i => s*x[i] + y[i]) := by simp done
         example (s r : ℝ ) (x y z  : C) : saxsrypnz s r x y z = intro (λ i => s*x[i] - r*y[i] + -z[i]) := by simp done
       end tests
     end VectorOperations

  end VectorSpace

  -- This provides something like Eigen's expression templates
  section LazyOperations

     section ElementWise
       variable {ι : Type v}
       variable {C : Type u} {α : Type w} [Cont C ι α]
       variable {C' : Type u'} {α' : Type w'} [Cont C' ι α']

       -- instance : Cont C (indexOf (self := instContData C ι α) C) (valueOf (self := instContData C ι α) C) := sorry

       instance [HAdd α α' β] : HAdd C C' (ι ↦ β) := ⟨λ c c' => λ i => c[i] + c'[i]⟩
       instance [HSub α α' β] : HSub C C' (ι ↦ β) := ⟨λ c c' => λ i => c[i] - c'[i]⟩
       instance [HMul α α' β] : HMul C C' (ι ↦ β) := ⟨λ c c' => λ i => c[i] * c'[i]⟩
       instance [HDiv α α' β] : HDiv C C' (ι ↦ β) := ⟨λ c c' => λ i => c[i] / c'[i]⟩

       @[simp] theorem elwise_hadd_apply [HAdd α α' β] (c : C) (c' : C') (i) : (c + c')[i] = c[i] + c'[i] := by simp[HAdd.hAdd] done
       @[simp] theorem elwise_hsub_apply [HSub α α' β] (c : C) (c' : C') (i) : (c - c')[i] = c[i] - c'[i] := by simp[HSub.hSub] done
       @[simp] theorem elwise_hmul_apply [HMul α α' β] (c : C) (c' : C') (i) : (c * c')[i] = c[i] * c'[i] := by simp[HMul.hMul] done
       @[simp] theorem elwise_hdiv_apply [HDiv α α' β] (c : C) (c' : C') (i) : (c / c')[i] = c[i] / c'[i] := by simp[HDiv.hDiv] done

     end ElementWise

     --- Matrix style multiplication
     section Mul
       variable {ι κ μ : Type v}
       variable {C : Type u} {α : Type w} [Cont C (ι×κ) α]
       variable {C' : Type u'} {α' : Type w'} [Cont C' (κ×μ) α']

       instance [HMul α α' β] [Add β] [Zero β] [Enumtype κ] 
                : HMul C C' (ι × μ ↦ β) 
                := ⟨λ c c' (i,j) => ∑ k, c[i,fromFin k] * c'[fromFin k,j]⟩

       @[simp] theorem hmul_apply [HMul α α' β] [Add β] [Zero β] [Enumtype κ]
                       (c : C) (c' : C')
                       : (c*c')[i,j] = ∑ k, c[i,fromFin k] * c'[fromFin k,j]
                       := by simp[HMul.hMul,Mul.mul] done

     end Mul

     section Broadcasting

       -- still not sure how to state theorems and instances about `Cont`
       -- variable {C : Type u} [ContData C] [Cont C (indexOf C) (valueOf C)] [Intro C]
       variable {C : Type u} {ι : Type v} {α : Type w} [Cont C ι α]

       -- Thise two can lead to ambiquous notation, we prefer the later
       -- i.e. The class `HAdd C (ι ↦ α) (ι ↦ ι ↦ α)` class has two different instance that are not equal!!!
       -- The second one ensures that `(c + b)[i] = c[i] + b[i]`
       instance (priority := low) [Add α] : HAdd C α (ι ↦ α) := ⟨λ c a i => c[i]+a⟩
       instance (priority := low) [Add α] : HAdd α C (ι ↦ α) := ⟨λ a c i => a+c[i]⟩
       instance [HAdd α β α] : HAdd C (ι ↦ β) (ι ↦ α) := ⟨λ c b i => c[i]+b[i]⟩
       instance [HAdd β α α] : HAdd (ι ↦ β) C (ι ↦ α) := ⟨λ b c i => b[i]+c[i]⟩

       instance (priority := low) [Sub α] : HSub C α (ι ↦ α) := ⟨λ c a i => c[i]-a⟩
       instance (priority := low) [Sub α] : HSub α C (ι ↦ α) := ⟨λ a c i => a-c[i]⟩
       instance [HSub α β α] : HSub C (ι ↦ β) (ι ↦ α) := ⟨λ c b i => c[i]-b[i]⟩
       instance [HSub β α α] : HSub (ι ↦ β) C (ι ↦ α) := ⟨λ b c i => b[i]-c[i]⟩

       -- We need to set higher priority to override instance `instContVecHMul : HMul ℝ C C`
       -- For some reason setting `low` priority on `instContVecHMul` does not work. 
       -- Not sure why is that and I simple mwe did not reproduce it ...
       instance (priority := mid+1) [HMul α β α] : HMul C β (ι ↦ α) := ⟨λ c b i => c[i]*b⟩
       instance (priority := mid+1) [HMul β α α] : HMul β C (ι ↦ α) := ⟨λ b c i => b*c[i]⟩
       instance (priority := mid+2) [HMul α β α] : HMul C (ι ↦ β) (ι ↦ α) := ⟨λ c b i => c[i]*b[i]⟩
       instance (priority := mid+2) [HMul β α α] : HMul (ι ↦ β) C (ι ↦ α) := ⟨λ b c i => b[i]*c[i]⟩

       instance (priority := low) [Div α] : HDiv C α (ι ↦ α) := ⟨λ c a i => c[i]/a⟩
       instance (priority := low) [Div α] : HDiv α C (ι ↦ α) := ⟨λ a c i => a/c[i]⟩
       instance [HDiv α β α] : HDiv C (ι ↦ β) (ι ↦ α) := ⟨λ c b i => c[i]/b[i]⟩
       instance [HDiv β α α] : HDiv (ι ↦ β) C (ι ↦ α) := ⟨λ b c i => b[i]/c[i]⟩    

       @[simp] theorem hadd_apply_1 [Add α] (c : C) (a : α) (i) : (c + a)[i] = c[i] + a := by simp[HAdd.hAdd] done
       @[simp] theorem hadd_apply_2 [Add α] (c : C) (a : α) (i) : (a + c)[i] = a + c[i] := by simp[HAdd.hAdd] done
       @[simp] theorem hadd_apply_3 [HAdd α β α] (c : C) (b : ι ↦ β) (i) : (c + b)[i] = c[i] + b[i] := by simp[HAdd.hAdd] done
       @[simp] theorem hadd_apply_4 [HAdd β α α] (c : C) (b : ι ↦ β) (i) : (b + c)[i] = b[i] + c[i] := by simp[HAdd.hAdd] done

       @[simp] theorem hsub_apply_1 [Sub α] (c : C) (a : α) (i) : (c - a)[i] = c[i] - a := by simp[HSub.hSub] done
       @[simp] theorem hsub_apply_2 [Sub α] (c : C) (a : α) (i) : (a - c)[i] = a - c[i] := by simp[HSub.hSub] done
       @[simp] theorem hsub_apply_3 [HSub α β α] (c : C) (b : ι ↦ β) (i) : (c - b)[i] = c[i] - b[i] := by simp[HSub.hSub] done
       @[simp] theorem hsub_apply_4 [HSub β α α] (c : C) (b : ι ↦ β) (i) : (b - c)[i] = b[i] - c[i] := by simp[HSub.hSub] done

       @[simp] theorem hmul_apply_1 [Mul α] (c : C) (a : α) (i) : (c * a)[i] = c[i] * a := by simp[HMul.hMul] done
       @[simp] theorem hmul_apply_2 [Mul α] (c : C) (a : α) (i) : (a * c)[i] = a * c[i] := by simp[HMul.hMul] done
       @[simp] theorem hmul_apply_3 [HMul α β α] (c : C) (b : ι ↦ β) (i) : (c * b)[i] = c[i] * b[i] := by simp[HMul.hMul] done
       @[simp] theorem hmul_apply_4 [HMul β α α] (c : C) (b : ι ↦ β) (i) : (b * c)[i] = b[i] * c[i] := by simp[HMul.hMul] done

       @[simp] theorem hdiv_apply_1 [Div α] (c : C) (a : α) (i) : (c / a)[i] = c[i] / a := by simp[HDiv.hDiv] done
       @[simp] theorem hdiv_apply_2 [Div α] (c : C) (a : α) (i) : (a / c)[i] = a / c[i] := by simp[HDiv.hDiv] done
       @[simp] theorem hdiv_apply_3 [HDiv α β α] (c : C) (b : ι ↦ β) (i) : (c / b)[i] = c[i] / b[i] := by simp[HDiv.hDiv] done
       @[simp] theorem hdiv_apply_4 [HDiv β α α] (c : C) (b : ι ↦ β) (i) : (b / c)[i] = b[i] / c[i] := by simp[HDiv.hDiv] done

     end Broadcasting

     -- Testing that arithmetic operations work which ever way we declare `Cont`
     section DeclType1
       variable {C : Type u} [ContData C] [Cont C (indexOf C) (valueOf C)] [Vec (valueOf C)] [Intro C]
       example (c d : C) : (indexOf C) ↦ (valueOf C) := c + d
       example (c : C) : (indexOf C) ↦ (valueOf C) := ((1 : ℝ)*c) 
     end DeclType1
     section DeclType2
       variable {C : Type u} {α : Type w} {ι : Type v} [Cont C ι α] [Vec α] [Intro C]
       example (c d : C) : ι ↦ α := c + d
       example (c : C) : ι ↦ α := ((1 : ℝ)*c)
     end DeclType2

     variable (A : Fin n × Fin m ↦ ℝ)
     -- variable {ι α : Type} (norm : (ι → α) → α)

     -- curry
     example : Fin n ↦ Fin m ↦ ℝ := (cont i j => A[i,j])
     -- example : A[:₀,:₁] = (cont i j => A[i,j]) := by rfl

     -- curry and swap
     example : Fin m ↦ Fin n ↦ ℝ := (cont j i => A[i,j])
     -- example : A[:₁,:₀] = (cont j i => A[i,j]) := by rfl

     -- transpose
     example : Fin m × Fin n ↦ ℝ := λ (i,j) => A[j,i] 
     -- example : (A[:₁,:₀])[:,:] = cont (i,j) => A[j,i] := by rfl

     -- sum rows v1
     example : Fin n ↦ ℝ := (∑ j, cont i => A[i,j]) 
     -- example : (∑ j, A[:,j]) = (∑ j, cont i => A[i,j]) := by rfl

     -- sum rows v2
     example : Fin n ↦ ℝ := (cont i => ∑ j, A[i,j])
     example : (∑ j, A[·,j]) = (cont i => ∑ j, A[i,j]) := by rfl
     example : (cont i => ∑ j, A[i,j]) = (∑ j, cont i => A[i,j]) := by funext i; admit  --- TODO: (∑ i, f i) x = (∑ i, f i x)

     -- center columns -- common task in data analysis
     example : Fin n × Fin m ↦ ℝ := λ (i,j) => A[i,j] - ∑ j', A[i,j']
     -- example : (A[:₀,:₁] - ∑ j', A[:,j'])[:,:] = cont (i,j) => A[i,j] - ∑ j', A[i,j'] := by rfl
     --- Future notation:  
     --      A[:₀,:₁]                  : Fin n ↦ Fin m ↦ ℝ
     --      ∑ j', A[:,j']             : Fin n          ↦ ℝ
     --      A[:₀,:₁] - ∑ j', A[:,j']  : Fin n ↦ Fin m ↦ ℝ
     -- 
     --- Alternatively:
     --      A[:₁,:₀]                  : Fin m ↦ Fin n ↦ ℝ
     --      ∑ j', A[:,j']             :          Fin n ↦ ℝ
     --      A[:₁,:₀] - ∑ j', A[:,j']  : Fin m ↦ Fin n ↦ ℝ
  
     -- This is ambiguous if `n == m` and we prefer the first one!

     variable (M : Fin n × Fin n ↦ ℝ)
     example : Fin n ↦ Fin n ↦ ℝ := (cont i j => M[i,j]) - (cont i => ∑' j, M[i,j])  --- This is ambiguous notation! Not clear what should be prefered?
     example : (cont i j => M[i,j]) - (∑' j, cont i => M[i,j]) = (cont i j => M[i,j] - ∑' j', M[i,j']) := by funext x y; simp[HSub.hSub,Sub.sub]; admit  --- TODO: (∑' i, f i) x = (∑' i, f i x)
     -- example : (cont i j => M[i,j]) - (∑' j, cont i => M[i,j]) = (cont i j => M[i,j] - ∑' j', M[j,j']) := NOT TRUE


     -- normalize columns
     example : Fin n × Fin m ↦ ℝ := λ (i,j) => A[i,j] / ∥λ i' => A[i',j]∥
     -- example : A[:₁,:₀] / (cont j => ∥A[:,j]∥) = (λ (i,j) => A[i,j] / Math.sqrt (∑ i', A[i',j]*A[i',j])) := by rfl
     example : (cont j i => A[i,j]) / (cont j => ∥λ i => A[i,j]∥) = (cont j i => A[i,j] / ∥λ i' => A[i',j]∥) := sorry
     -- example : M[:₁,:₀] / (cont j => ∥A[:,j]∥) = (λ (i,j) => A[i,j] / Math.sqrt (∑ i', A[i',j]*A[i',j])) := by rfl

  end LazyOperations


  section ForNotation

    -- Usefull for modifying a container as we want to run only over indices and not values
    open Enumtype in 
    def allIdx {C} (c : C) [ContData C] [Enumtype (indexOf C)] : Range (indexOf C) := fullRange (indexOf C)

    -- notation:  
    --      for (a,i,li) in F do
    --          ..                        
    open Enumtype in
    instance {m} [Monad m] {ι} {α : Type w} [Enumtype ι] [ForIn m (Range ι) (ι × Nat)]
             : ForIn m (ι ↦ α) (α × ι × Nat) :=
    {
      forIn := λ F init f => do
                 let mut val := init
                 for (i,li) in fullRange ι do
                   match (← f (F[i], i, li) val) with
                   | ForInStep.done d => return d
                   | ForInStep.yield d => val ← d
                 pure init
    }

  
    def test : IO Unit := do
        let mut val : Nat := 0
        for (a,i,li) in (cont i : Fin 2 × Fin 3 × Fin 4 => ()) do 
           val := val + li
           IO.println s!"i = {i}  |  li = {li}  |  a = {a}  |  val = {val}"
        IO.println s!"val = {val}"

    #eval test

    def test2 : IO Unit := do
        let mut val : Nat := 0
        for (a,i,li) in (cont i : Fin 2 ×ₗ Fin 3 ×ₗ Fin 4 => ()) do 
           val := val + li
           IO.println s!"i = {i}  |  li = {li}  |  a = {a}  |  val = {val}"
        IO.println s!"val = {val}"

    #eval test2

    
    def r : Enumtype.Range (Fin 10 × Fin 10) := some ((!5,!0),(!9,!4))
  
    def test4 : IO Unit := do
        let mut val : Nat := 0
        for (i,li) in r do 
           IO.println s!"i = {i}  |  li = {li} "

    #eval test4



  end ForNotation


  -- View of a container if usefull if you want to modify a subset of a container and still refer to it as a container
  section ContainerView

    def ContView {κ} (C : Type u) [ContData C] (tr : κ → (indexOf C)) := C
    def view   {κ} {C} [ContData C] (c : C) (tr : κ → (indexOf C)) : ContView C tr := c
    def unview {κ} {C} [ContData C] {tr : κ → (indexOf C)} (c : ContView C tr) : C := c

    instance {κ} (C : Type u) [ContData C] (tr : κ → (indexOf C)) : ContData (ContView C tr) :=
    {
      indexOf := κ
      valueOf := (valueOf C)
    }

    instance {C ι α κ} [Cont C ι α] (tr : κ → ι) : Cont (ContView C tr) κ α :=
    {
      toFun := λ c j => (unview c)[tr j]
    }
  
    instance {C ι α κ} [Cont C ι α] (tr : κ → ι) [Set C] : Set (ContView C tr) :=
    {
      set := λ c j a => view (set (unview c) (tr j) a) tr
      valid := sorry
    }

  end ContainerView

end Cont



