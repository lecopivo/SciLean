import Lean
import Batteries.Data.Array.Basic
import SciLean.Data.DataArray.DataArray

/-!
# Lazy Tensor Compiler

Inspired by tinygrad's architecture, this module implements lazy tensor evaluation
with kernel fusion and symbolic shape support.

## Implementation Status

**Implemented:**
- ✅ `Sint`: Symbolic integers with constant folding
- ✅ `LazyNode`: Lazy computation graph representation
- ✅ `LazyTensor`: User-facing lazy tensor API with Thunk
- ✅ Pattern matching for algebraic simplification (`x + 0 = x`, etc.)
- ✅ Gradient rules for reverse-mode AD on the graph
- ✅ Topological sort for proper backprop ordering
- ✅ Basic kernel fusion detection

**Not Yet Implemented:**
- ❌ Lowering `LazyNode` → `UOp` (micro-ops IR)
- ❌ Code generation from `UOp` to CUDA/Metal/C
- ❌ Actual execution backends (see `TensorBackend` trait)
- ❌ Integration with `DataArrayN` for seamless use

## Architecture

```
LazyTensor (graph building)
        |
        v
LazyNode (computation graph)
        |  <- algebraic simplification via pattern matching
        v
[TODO] UOp (micro-operations IR)
        |  <- code generation
        v
[TODO] Backend execution (BLAS/Metal/CUDA)
```

## Key Concepts from tinygrad

1. Lazy evaluation: Operations build a graph, only compute on realize
2. Kernel fusion: Adjacent elementwise ops become one kernel
3. Symbolic shapes: Dimensions can be variables, resolved at runtime
4. Pattern matching: Algebraic simplification via term rewriting
-/

namespace SciLean.Compiler

/-! ## Symbolic Integers

Like tinygrad's `sint`, these allow dimensions to be symbolic variables
that are resolved at runtime.
-/

/-- A symbolic integer: either a concrete Nat or a symbolic variable. -/
inductive Sint where
  | nat : Nat → Sint
  | var : String → Sint
  | add : Sint → Sint → Sint
  | sub : Sint → Sint → Sint
  | mul : Sint → Sint → Sint
  | div : Sint → Sint → Sint
  | mod : Sint → Sint → Sint
  | max : Sint → Sint → Sint
  | min : Sint → Sint → Sint
  deriving Repr, BEq, Hashable

namespace Sint

instance : OfNat Sint n where
  ofNat := Sint.nat n

instance : Add Sint where
  add := Sint.add

instance : Mul Sint where
  mul := Sint.mul

instance : Div Sint where
  div := Sint.div

instance : Mod Sint where
  mod := Sint.mod

instance : Sub Sint where
  sub := Sint.sub

/-- Simplify a symbolic integer by constant folding. -/
partial def simplify : Sint → Sint
  | nat n => nat n
  | var s => var s
  | add a b =>
    match simplify a, simplify b with
    | nat 0, b' => b'
    | a', nat 0 => a'
    | nat n, nat m => nat (n + m)
    | a', b' => add a' b'
  | sub a b =>
    match simplify a, simplify b with
    | a', nat 0 => a'
    | nat n, nat m => nat (n - m)
    | a', b' => sub a' b'
  | mul a b =>
    match simplify a, simplify b with
    | nat 0, _ => nat 0
    | _, nat 0 => nat 0
    | nat 1, b' => b'
    | a', nat 1 => a'
    | nat n, nat m => nat (n * m)
    | a', b' => mul a' b'
  | div a b =>
    match simplify a, simplify b with
    | nat n, nat m => if m ≠ 0 then nat (n / m) else div (nat n) (nat m)
    | a', nat 1 => a'
    | a', b' => div a' b'
  | mod a b =>
    match simplify a, simplify b with
    | nat n, nat m => if m ≠ 0 then nat (n % m) else mod (nat n) (nat m)
    | a', b' => mod a' b'
  | max a b =>
    match simplify a, simplify b with
    | nat n, nat m => nat (Nat.max n m)
    | a', b' => max a' b'
  | min a b =>
    match simplify a, simplify b with
    | nat n, nat m => nat (Nat.min n m)
    | a', b' => min a' b'

/-- Evaluate a symbolic integer given variable bindings. -/
def eval (vars : String → Nat) : Sint → Nat
  | nat n => n
  | var s => vars s
  | add a b => eval vars a + eval vars b
  | sub a b => eval vars a - eval vars b
  | mul a b => eval vars a * eval vars b
  | div a b => eval vars a / eval vars b
  | mod a b => eval vars a % eval vars b
  | max a b => Nat.max (eval vars a) (eval vars b)
  | min a b => Nat.min (eval vars a) (eval vars b)

end Sint

/-! ## Tensor Operations (like tinygrad's Ops)

The core operations that can appear in a lazy tensor graph.
-/

/-- Data types for tensors. -/
inductive DType where
  | float32 : DType
  | float64 : DType
  | int32 : DType
  | int64 : DType
  | bool : DType
  deriving Repr, BEq, Hashable

/-- Unary operations. -/
inductive UnaryOp where
  | neg : UnaryOp
  | exp2 : UnaryOp
  | log2 : UnaryOp
  | sin : UnaryOp
  | sqrt : UnaryOp
  | reciprocal : UnaryOp
  | cast : DType → UnaryOp
  deriving Repr, BEq, Hashable

/-- Binary operations. -/
inductive BinaryOp where
  | add : BinaryOp
  | sub : BinaryOp
  | mul : BinaryOp      -- elementwise multiplication
  | div : BinaryOp
  | max : BinaryOp
  | min : BinaryOp
  | cmpLt : BinaryOp
  | cmpEq : BinaryOp
  | matmul : BinaryOp   -- matrix multiplication
  deriving Repr, BEq, Hashable

/-- Reduce operations. -/
inductive ReduceOp where
  | sum : ReduceOp
  | max : ReduceOp
  | min : ReduceOp
  deriving Repr, BEq, Hashable

/-- Movement operations (reshape, permute, etc.). -/
inductive MovementOp where
  | reshape : Array Sint → MovementOp
  | permute : Array Nat → MovementOp
  | expand : Array Sint → MovementOp
  | pad : Array (Sint × Sint) → MovementOp
  | shrink : Array (Sint × Sint) → MovementOp
  | flip : Array Nat → MovementOp  -- flip along specified axes
  deriving Repr, BEq

namespace MovementOp

/-- Check if movement op is a no-op. -/
def isIdentity : MovementOp → Array Sint → Bool
  | .reshape s, inputShape => s == inputShape
  | .permute perm, _ => perm == Array.range perm.size
  | .expand s, inputShape => s == inputShape
  | .pad padding, _ => padding.all fun (lo, hi) => lo == Sint.nat 0 && hi == Sint.nat 0
  | .shrink _, _ => false  -- shrink is never identity unless full range
  | .flip axes, _ => axes.isEmpty

/-- Compose two permutations. -/
def composePermute (p1 p2 : Array Nat) : Array Nat :=
  p2.map fun i => p1.getD i 0

/-- Try to fuse two movement ops. -/
def fuse : MovementOp → MovementOp → Option MovementOp
  | .permute p1, .permute p2 => some (.permute (composePermute p1 p2))
  | .reshape _, .reshape s2 => some (.reshape s2)  -- reshape ∘ reshape = reshape
  | .flip a1, .flip a2 =>
    -- flipping same axis twice cancels out
    let combined := (a1 ++ a2).filter fun ax =>
      let count := (a1 ++ a2).filter (· == ax) |>.size
      count % 2 == 1
    some (.flip combined)
  | _, _ => none

end MovementOp

/-! ## Lazy Tensor Graph

A lazy tensor is a thunk that builds a computation graph.
Operations on lazy tensors don't compute immediately - they build the graph.
Only when `.realize()` is called does computation happen.
-/

/-- A node in the lazy computation graph. -/
inductive LazyNode where
  | buffer : Nat → Array Sint → DType → LazyNode  -- id, shape, dtype
  | const : Float → Array Sint → DType → LazyNode
  | unary : UnaryOp → LazyNode → LazyNode
  | binary : BinaryOp → LazyNode → LazyNode → LazyNode
  | reduce : ReduceOp → Array Nat → LazyNode → LazyNode  -- axes to reduce
  | movement : MovementOp → LazyNode → LazyNode
  deriving Repr

instance : Inhabited LazyNode where
  default := .const 0.0 #[] .float32

/-- Structural equality for LazyNode. -/
partial def LazyNode.beq : LazyNode → LazyNode → Bool
  | .buffer id1 shape1 dt1, .buffer id2 shape2 dt2 =>
    id1 == id2 && shape1 == shape2 && dt1 == dt2
  | .const v1 shape1 dt1, .const v2 shape2 dt2 =>
    v1 == v2 && shape1 == shape2 && dt1 == dt2
  | .unary op1 x1, .unary op2 x2 =>
    op1 == op2 && x1.beq x2
  | .binary op1 x1 y1, .binary op2 x2 y2 =>
    op1 == op2 && x1.beq x2 && y1.beq y2
  | .reduce op1 axes1 x1, .reduce op2 axes2 x2 =>
    op1 == op2 && axes1 == axes2 && x1.beq x2
  | .movement op1 x1, .movement op2 x2 =>
    op1 == op2 && x1.beq x2
  | _, _ => false

instance : BEq LazyNode where
  beq := LazyNode.beq

/-- Hash for LazyNode (for use in HashMaps, not equality). -/
partial def LazyNode.toHash : LazyNode → UInt64
  | .buffer id shape _ =>
    mixHash id.toUInt64 shape.size.toUInt64
  | .const v shape _ =>
    mixHash v.toUInt64 shape.size.toUInt64
  | .unary op x =>
    mixHash (Hashable.hash op) x.toHash
  | .binary op x y =>
    mixHash (Hashable.hash op) (mixHash x.toHash y.toHash)
  | .reduce op axes x =>
    mixHash (Hashable.hash op) (mixHash axes.size.toUInt64 x.toHash)
  | .movement _ x =>
    mixHash 7 x.toHash

instance : Hashable LazyNode where
  hash n := n.toHash

namespace LazyNode

/-- Get the shape of a lazy node. -/
def shape : LazyNode → Array Sint
  | buffer _ s _ => s
  | const _ s _ => s
  | unary _ x => x.shape
  | binary .matmul x y =>
    -- matmul: [..., m, k] @ [..., k, n] -> [..., m, n]
    let sx := x.shape
    let sy := y.shape
    if sx.size < 2 || sy.size < 2 then sx  -- fallback for malformed input
    else
      let m := sx.getD (sx.size - 2) (Sint.nat 0)
      let n := sy.getD (sy.size - 1) (Sint.nat 0)
      sx.pop.pop ++ #[m, n]
  | binary _ x _ => x.shape  -- assumes broadcasting resolved for other ops
  | reduce _ axes x =>
    let s := x.shape
    s.mapIdx fun i si => if axes.contains i then Sint.nat 1 else si
  | movement op x =>
    match op with
    | .reshape s => s
    | .permute perm => perm.map (x.shape.getD · (Sint.nat 0))
    | .expand s => s
    | .pad padding =>
      x.shape.mapIdx fun i si =>
        let (lo, hi) := padding.getD i (Sint.nat 0, Sint.nat 0)
        si + lo + hi
    | .shrink bounds =>
      bounds.map fun (lo, hi) => hi - lo
    | .flip _ => x.shape  -- flip doesn't change shape

/-- Get the dtype of a lazy node. -/
def dtype : LazyNode → DType
  | buffer _ _ d => d
  | const _ _ d => d
  | unary (.cast d) _ => d
  | unary _ x => x.dtype
  | binary .cmpLt _ _ => .bool
  | binary .cmpEq _ _ => .bool
  | binary _ x _ => x.dtype
  | reduce _ _ x => x.dtype
  | movement _ x => x.dtype

end LazyNode

/-! ## Pattern Matching for Optimization

Like tinygrad's PatternMatcher, we define rewrite rules for algebraic simplification.
-/

/-- A pattern for matching lazy nodes. -/
inductive Pattern where
  | any : String → Pattern  -- matches anything, binds to name
  | const : Float → Pattern
  | unary : UnaryOp → Pattern → Pattern
  | binary : BinaryOp → Pattern → Pattern → Pattern
  deriving Repr

/-- Result of pattern matching. -/
abbrev MatchResult := Option (List (String × LazyNode))

/-- Match a pattern against a lazy node. -/
def matchPattern (p : Pattern) (n : LazyNode) : MatchResult :=
  match p, n with
  | .any name, _ => some [(name, n)]
  | .const c, .const c' _ _ => if c == c' then some [] else none
  | .unary op p', .unary op' n' =>
    if op == op' then matchPattern p' n' else none
  | .binary op p1 p2, .binary op' n1 n2 =>
    if op == op' then do
      let m1 ← matchPattern p1 n1
      let m2 ← matchPattern p2 n2
      return m1 ++ m2
    else none
  | _, _ => none

/-- A rewrite rule: pattern → replacement function. -/
structure RewriteRule where
  pattern : Pattern
  rewrite : List (String × LazyNode) → Option LazyNode

/-- Apply rewrite rules until fixpoint. -/
partial def applyRules (rules : List RewriteRule) (n : LazyNode) : LazyNode :=
  let tryRule (n : LazyNode) : Option LazyNode :=
    rules.findSome? fun rule =>
      matchPattern rule.pattern n >>= rule.rewrite

  match tryRule n with
  | some n' => applyRules rules n'
  | none =>
    match n with
    | .unary op x => .unary op (applyRules rules x)
    | .binary op x y => .binary op (applyRules rules x) (applyRules rules y)
    | .reduce op axes x => .reduce op axes (applyRules rules x)
    | .movement op x => .movement op (applyRules rules x)
    | _ => n

/-! ## Standard Simplification Rules

Algebraic identities like `x + 0 = x`, `x * 1 = x`, etc.
-/

def standardRules : List RewriteRule := [
  -- x + 0 = x
  { pattern := .binary .add (.any "x") (.const 0)
    rewrite := fun bindings =>
      bindings.find? (·.1 == "x") |>.map (·.2) },
  -- 0 + x = x
  { pattern := .binary .add (.const 0) (.any "x")
    rewrite := fun bindings =>
      bindings.find? (·.1 == "x") |>.map (·.2) },
  -- x * 1 = x
  { pattern := .binary .mul (.any "x") (.const 1)
    rewrite := fun bindings =>
      bindings.find? (·.1 == "x") |>.map (·.2) },
  -- 1 * x = x
  { pattern := .binary .mul (.const 1) (.any "x")
    rewrite := fun bindings =>
      bindings.find? (·.1 == "x") |>.map (·.2) },
  -- x * 0 = 0
  { pattern := .binary .mul (.any "_") (.const 0)
    rewrite := fun _ => some (.const 0 #[] .float32) },
  -- 0 * x = 0
  { pattern := .binary .mul (.const 0) (.any "_")
    rewrite := fun _ => some (.const 0 #[] .float32) }
]

/-! ## Lazy Tensor API

The user-facing lazy tensor type that wraps LazyNode in a Thunk.
-/

/-- A lazy tensor that defers computation until realized. -/
structure LazyTensor where
  node : Thunk LazyNode

instance : Inhabited LazyTensor where
  default := { node := Thunk.mk fun _ => default }

namespace LazyTensor

/-- Create a lazy tensor from a buffer reference. -/
def fromBuffer (id : Nat) (shape : Array Sint) (dtype : DType := .float32) : LazyTensor :=
  { node := Thunk.mk fun _ => .buffer id shape dtype }

/-- Create a lazy tensor from a constant. -/
def const (value : Float) (shape : Array Sint) (dtype : DType := .float32) : LazyTensor :=
  { node := Thunk.mk fun _ => .const value shape dtype }

/-- Elementwise negation. -/
def neg (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .unary .neg x.node.get }

/-- Elementwise addition. -/
def add (x y : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .binary .add x.node.get y.node.get }

/-- Elementwise multiplication. -/
def mul (x y : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .binary .mul x.node.get y.node.get }

/-- Elementwise subtraction. -/
def sub (x y : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .binary .sub x.node.get y.node.get }

/-- Elementwise division. -/
def div (x y : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .binary .div x.node.get y.node.get }

/-- Reduce sum along axes. -/
def sum (axes : Array Nat) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .reduce .sum axes x.node.get }

/-- Reduce max along axes. -/
def max (axes : Array Nat) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .reduce .max axes x.node.get }

/-- Reshape tensor. -/
def reshape (newShape : Array Sint) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .movement (.reshape newShape) x.node.get }

/-- Permute tensor dimensions. -/
def permute (perm : Array Nat) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .movement (.permute perm) x.node.get }

/-- Expand tensor to new shape (broadcast). -/
def expand (newShape : Array Sint) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .movement (.expand newShape) x.node.get }

/-- Pad tensor with zeros. -/
def pad (padding : Array (Sint × Sint)) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .movement (.pad padding) x.node.get }

/-- Shrink tensor (slice). -/
def shrink (bounds : Array (Sint × Sint)) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .movement (.shrink bounds) x.node.get }

/-- Flip tensor along axes. -/
def flip (axes : Array Nat) (x : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .movement (.flip axes) x.node.get }

/-- Transpose (swap last two dimensions). -/
def transpose (x : LazyTensor) : LazyTensor :=
  let shape := x.node.get.shape
  let n := shape.size
  if n < 2 then x
  else
    let perm := Array.range n |>.modify (n - 2) (fun _ => n - 1) |>.modify (n - 1) (fun _ => n - 2)
    permute perm x

/-- Matrix multiplication. -/
def matmul (x y : LazyTensor) : LazyTensor :=
  { node := Thunk.mk fun _ => .binary .matmul x.node.get y.node.get }

/-- Force evaluation of the lazy tensor graph. -/
def realize (x : LazyTensor) : LazyNode :=
  let node := x.node.get
  applyRules standardRules node

instance : Add LazyTensor := ⟨add⟩
instance : Mul LazyTensor := ⟨mul⟩
instance : Sub LazyTensor := ⟨sub⟩
instance : Div LazyTensor := ⟨div⟩
instance : Neg LazyTensor := ⟨neg⟩

end LazyTensor

/-! ## UOp: Micro-Operations IR

Like tinygrad's UOp, this is the core intermediate representation.
All tensor operations get lowered to UOp before code generation.

**Status**: Defined but not yet used. Lowering from `LazyNode` to `UOp` is TODO.
-/

/-- Axis types for GPU execution dimensions. -/
inductive AxisType where
  | global : AxisType  -- GPU global dimensions
  | warp : AxisType    -- Warp-level parallelism
  | local_ : AxisType  -- Shared memory / local
  | loop : AxisType    -- Loop iterations
  | reduce : AxisType  -- Reduction dimension
  | upcast : AxisType  -- Vector width
  deriving Repr, BEq, Hashable

/-- A micro-operation in the computation graph.

This is the core IR that all operations get lowered to.
Unlike `LazyNode`, `UOp` is designed for code generation:
- Explicit memory operations (LOAD, STORE, INDEX)
- Control flow (RANGE, IF, BARRIER)
- GPU-specific operations (WMMA for tensor cores)
-/
inductive UOp where
  | const : Float → DType → UOp
  | defineGlobal : Nat → DType → UOp   -- Buffer reference
  | defineVar : String → UOp           -- Symbolic variable
  | load : UOp → UOp                   -- Load from memory
  | store : UOp → UOp → UOp            -- Store to memory (ptr, value)
  | index : UOp → UOp → UOp            -- Pointer arithmetic
  | range : Sint → Sint → AxisType → UOp  -- Loop range
  | barrier : UOp                       -- GPU barrier
  -- ALU ops
  | neg : UOp → UOp
  | exp2 : UOp → UOp
  | log2 : UOp → UOp
  | sin : UOp → UOp
  | sqrt : UOp → UOp
  | recip : UOp → UOp
  | add : UOp → UOp → UOp
  | sub : UOp → UOp → UOp
  | mul : UOp → UOp → UOp
  | div : UOp → UOp → UOp
  | max : UOp → UOp → UOp
  | cmpLt : UOp → UOp → UOp
  | cmpEq : UOp → UOp → UOp
  | where_ : UOp → UOp → UOp → UOp  -- ternary conditional
  | mulacc : UOp → UOp → UOp → UOp  -- multiply-accumulate
  deriving Repr

instance : Inhabited UOp where
  default := .const 0.0 .float32

/-- Structural equality for UOp. -/
partial def UOp.beq : UOp → UOp → Bool
  | .const v1 dt1, .const v2 dt2 => v1 == v2 && dt1 == dt2
  | .defineGlobal id1 dt1, .defineGlobal id2 dt2 => id1 == id2 && dt1 == dt2
  | .defineVar s1, .defineVar s2 => s1 == s2
  | .load u1, .load u2 => u1.beq u2
  | .store p1 v1, .store p2 v2 => p1.beq p2 && v1.beq v2
  | .index b1 o1, .index b2 o2 => b1.beq b2 && o1.beq o2
  | .range lo1 hi1 ax1, .range lo2 hi2 ax2 => lo1 == lo2 && hi1 == hi2 && ax1 == ax2
  | .barrier, .barrier => true
  | .neg u1, .neg u2 => u1.beq u2
  | .exp2 u1, .exp2 u2 => u1.beq u2
  | .log2 u1, .log2 u2 => u1.beq u2
  | .sin u1, .sin u2 => u1.beq u2
  | .sqrt u1, .sqrt u2 => u1.beq u2
  | .recip u1, .recip u2 => u1.beq u2
  | .add x1 y1, .add x2 y2 => x1.beq x2 && y1.beq y2
  | .sub x1 y1, .sub x2 y2 => x1.beq x2 && y1.beq y2
  | .mul x1 y1, .mul x2 y2 => x1.beq x2 && y1.beq y2
  | .div x1 y1, .div x2 y2 => x1.beq x2 && y1.beq y2
  | .max x1 y1, .max x2 y2 => x1.beq x2 && y1.beq y2
  | .cmpLt x1 y1, .cmpLt x2 y2 => x1.beq x2 && y1.beq y2
  | .cmpEq x1 y1, .cmpEq x2 y2 => x1.beq x2 && y1.beq y2
  | .where_ c1 t1 f1, .where_ c2 t2 f2 => c1.beq c2 && t1.beq t2 && f1.beq f2
  | .mulacc a1 b1 c1, .mulacc a2 b2 c2 => a1.beq a2 && b1.beq b2 && c1.beq c2
  | _, _ => false

instance : BEq UOp where
  beq := UOp.beq

/-! ## Gradient Rules via Pattern Matching

Like tinygrad's `pm_gradient`, we define gradient rules as pattern matches.
Each rule maps an operation to its backward pass.
-/

/-- Result of gradient computation: one gradient per input. -/
abbrev GradResult := List (Option LazyNode)

/-- A gradient rule: matches an operation and produces gradients for its inputs. -/
structure GradientRule where
  /-- Name for debugging -/
  name : String
  /-- Match function: returns true if this rule applies -/
  matchNode : LazyNode → Bool
  /-- Gradient function: given ctx and ret produces input gradients -/
  gradFn : LazyNode → LazyNode → GradResult

/-- Standard gradient rules for common operations. -/
def gradientRules : List GradientRule := [
  -- Negation: d/dx (-x) = -1, so grad = -ctx
  { name := "neg"
    matchNode := fun n => match n with | .unary .neg _ => true | _ => false
    gradFn := fun ctx _ => [some (.unary .neg ctx)] },

  -- Addition: d/dx (x + y) = 1 for both inputs
  { name := "add"
    matchNode := fun n => match n with | .binary .add _ _ => true | _ => false
    gradFn := fun ctx _ => [some ctx, some ctx] },

  -- Subtraction: d/dx (x - y) = 1, d/dy (x - y) = -1
  { name := "sub"
    matchNode := fun n => match n with | .binary .sub _ _ => true | _ => false
    gradFn := fun ctx _ => [some ctx, some (.unary .neg ctx)] },

  -- Multiplication: d/dx (x * y) = y, d/dy (x * y) = x (product rule)
  { name := "mul"
    matchNode := fun n => match n with | .binary .mul _ _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .binary .mul x y => [some (.binary .mul ctx y), some (.binary .mul ctx x)]
      | _ => [] },

  -- Division: d/dx (x / y) = 1/y, d/dy (x / y) = -x/y²
  { name := "div"
    matchNode := fun n => match n with | .binary .div _ _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .binary .div x y =>
        let gradX := .binary .div ctx y
        let gradY := .unary .neg (.binary .div (.binary .mul ctx x) (.binary .mul y y))
        [some gradX, some gradY]
      | _ => [] },

  -- exp2: d/dx 2^x = 2^x * ln(2), so grad = ret * ctx * ln(2)
  { name := "exp2"
    matchNode := fun n => match n with | .unary .exp2 _ => true | _ => false
    gradFn := fun ctx ret =>
      let ln2 := LazyNode.const 0.693147 #[] .float32
      [some (.binary .mul (.binary .mul ret ctx) ln2)] },

  -- log2: d/dx log2(x) = 1 / (x * ln(2)), so grad = ctx / (x * ln(2))
  { name := "log2"
    matchNode := fun n => match n with | .unary .log2 _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .unary .log2 x =>
        let ln2 := LazyNode.const 0.693147 #[] .float32
        [some (.binary .div ctx (.binary .mul x ln2))]
      | _ => [] },

  -- sin: d/dx sin(x) = cos(x) = sin(x + π/2)
  { name := "sin"
    matchNode := fun n => match n with | .unary .sin _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .unary .sin x =>
        let piOver2 := LazyNode.const 1.5707963 #[] .float32
        let cos := LazyNode.unary .sin (.binary .add x piOver2)
        [some (.binary .mul ctx cos)]
      | _ => [] },

  -- sqrt: d/dx sqrt(x) = 1 / (2 * sqrt(x)), so grad = ctx / (2 * ret)
  { name := "sqrt"
    matchNode := fun n => match n with | .unary .sqrt _ => true | _ => false
    gradFn := fun ctx ret =>
      let two := LazyNode.const 2.0 #[] .float32
      [some (.binary .div ctx (.binary .mul two ret))] },

  -- reciprocal: d/dx (1/x) = -1/x², so grad = -ctx * ret²
  { name := "reciprocal"
    matchNode := fun n => match n with | .unary .reciprocal _ => true | _ => false
    gradFn := fun ctx ret =>
      [some (.unary .neg (.binary .mul ctx (.binary .mul ret ret)))] },

  -- matmul: d/dA (A @ B) = dOut @ B^T, d/dB (A @ B) = A^T @ dOut
  { name := "matmul"
    matchNode := fun n => match n with | .binary .matmul _ _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .binary .matmul a b =>
        -- Transpose helper: swap last two dimensions
        let transposeNode (x : LazyNode) : LazyNode :=
          let n := x.shape.size
          if n < 2 then x
          else
            let perm := Array.range n |>.modify (n - 2) (fun _ => n - 1) |>.modify (n - 1) (fun _ => n - 2)
            .movement (.permute perm) x
        let gradA := .binary .matmul ctx (transposeNode b)
        let gradB := .binary .matmul (transposeNode a) ctx
        [some gradA, some gradB]
      | _ => [] }
]

/-- Movement operation gradient rules. -/
def movementGradientRules : List GradientRule := [
  -- reshape: gradient is reshaped back to input shape
  { name := "reshape"
    matchNode := fun n => match n with | .movement (.reshape _) _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .movement (.reshape _) x => [some (.movement (.reshape x.shape) ctx)]
      | _ => [] },

  -- permute: gradient uses inverse permutation
  { name := "permute"
    matchNode := fun n => match n with | .movement (.permute _) _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .movement (.permute perm) _ =>
        -- Compute inverse permutation
        let invPerm := Array.range perm.size |>.map fun i =>
          perm.findIdx? (· == i) |>.getD 0
        [some (.movement (.permute invPerm) ctx)]
      | _ => [] },

  -- expand: gradient is reduced (summed) along expanded dimensions
  { name := "expand"
    matchNode := fun n => match n with | .movement (.expand _) _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .movement (.expand _) x =>
        -- Find axes where input had size 1 but output has size > 1
        let inputShape := x.shape
        let outputShape := ret.shape
        let reduceAxes := Array.range inputShape.size |>.filterMap fun i =>
          let si := inputShape.getD i (Sint.nat 0)
          let so := outputShape.getD i (Sint.nat 0)
          if si == Sint.nat 1 && so != Sint.nat 1 then some i else none
        if reduceAxes.isEmpty then [some ctx]
        else [some (.reduce .sum reduceAxes ctx)]
      | _ => [] },

  -- pad: gradient shrinks (removes padding)
  { name := "pad"
    matchNode := fun n => match n with | .movement (.pad _) _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .movement (.pad padding) x =>
        let bounds := Array.range x.shape.size |>.map fun i =>
          let si := x.shape.getD i (Sint.nat 0)
          let (lo, _) := padding.getD i (Sint.nat 0, Sint.nat 0)
          (lo, lo + si)
        [some (.movement (.shrink bounds) ctx)]
      | _ => [] },

  -- shrink: gradient pads back
  { name := "shrink"
    matchNode := fun n => match n with | .movement (.shrink _) _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .movement (.shrink bounds) x =>
        let padding := Array.range x.shape.size |>.map fun i =>
          let si := x.shape.getD i (Sint.nat 0)
          let (lo, hi) := bounds.getD i (Sint.nat 0, Sint.nat 0)
          (lo, si - hi)
        [some (.movement (.pad padding) ctx)]
      | _ => [] },

  -- flip: gradient flips along same axes
  { name := "flip"
    matchNode := fun n => match n with | .movement (.flip _) _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .movement (.flip axes) _ => [some (.movement (.flip axes) ctx)]
      | _ => [] }
]

/-- Reduce operation gradient rules. -/
def reduceGradientRules : List GradientRule := [
  -- sum: gradient broadcasts back to input shape
  { name := "reduce_sum"
    matchNode := fun n => match n with | .reduce .sum _ _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .reduce .sum _axes x =>
        -- Broadcast ctx back to input shape
        [some (.movement (.expand x.shape) ctx)]
      | _ => [] },

  -- max: gradient is 1 where input equals output, 0 elsewhere (subgradient)
  -- This is a simplified version - full impl needs the argmax
  { name := "reduce_max"
    matchNode := fun n => match n with | .reduce .max _ _ => true | _ => false
    gradFn := fun ctx ret =>
      match ret with
      | .reduce .max _axes x =>
        -- Expand output to input shape, then mask where input == output
        let expandedOut := LazyNode.movement (.expand x.shape) ret
        let expandedCtx := LazyNode.movement (.expand x.shape) ctx
        let mask := LazyNode.binary .cmpEq x expandedOut
        -- Cast bool to float and multiply
        let maskFloat := LazyNode.unary (.cast .float32) mask
        [some (.binary .mul expandedCtx maskFloat)]
      | _ => [] }
]

/-- All gradient rules combined. -/
def allGradientRules : List GradientRule :=
  gradientRules ++ movementGradientRules ++ reduceGradientRules

/-- Look up the gradient rule for a node. -/
def findGradientRule (n : LazyNode) : Option GradientRule :=
  allGradientRules.find? fun rule => rule.matchNode n

/-! ## Topological Sort

Proper reverse-mode AD requires processing nodes in reverse topological order.
-/

/-- Get all children of a node. -/
def LazyNode.children : LazyNode → List LazyNode
  | .buffer _ _ _ => []
  | .const _ _ _ => []
  | .unary _ x => [x]
  | .binary _ x y => [x, y]
  | .reduce _ _ x => [x]
  | .movement _ x => [x]

/-- Topological sort of computation graph (returns nodes in forward order). -/
partial def toposort (root : LazyNode) : List LazyNode :=
  let rec visit (node : LazyNode) (visited : List LazyNode) : List LazyNode :=
    if visited.any (· == node) then visited
    else
      let visited' := node.children.foldl (fun acc child => visit child acc) visited
      visited' ++ [node]
  visit root []

/-- Compute gradients using proper reverse-mode AD with topological sort.

This implements backpropagation correctly:
1. Topologically sort the graph
2. Process nodes in reverse order
3. Accumulate gradients at each node
-/
partial def computeGradients
    (root : LazyNode)
    (rootGrad : LazyNode)
    (targets : List LazyNode) : List (LazyNode × LazyNode) :=
  -- Get nodes in forward topological order
  let forwardOrder := toposort root

  -- Initialize gradient map with root gradient
  let initGrads : List (LazyNode × LazyNode) := [(root, rootGrad)]

  -- Process nodes in reverse order, accumulating gradients
  let finalGrads := forwardOrder.reverse.foldl (fun grads node =>
    match grads.find? (fun (n, _) => n == node) with
    | none => grads
    | some (_, nodeGrad) =>
      match findGradientRule node with
      | none => grads
      | some rule =>
        let inputGrads := rule.gradFn nodeGrad node
        let children := node.children
        -- Add gradients for each child
        children.zip inputGrads |>.foldl (fun acc (child, maybeGrad) =>
          match maybeGrad with
          | none => acc
          | some grad =>
            match acc.find? (fun (n, _) => n == child) with
            | none => acc ++ [(child, grad)]
            | some (_, existingGrad) =>
              -- Accumulate gradients
              let newGrad := LazyNode.binary .add existingGrad grad
              acc.map fun (n, g) => if n == child then (n, newGrad) else (n, g)
        ) grads
  ) initGrads

  -- Return only gradients for target nodes
  finalGrads.filter fun (node, _) => targets.any (· == node)

/-! ## Kernel Fusion (Scheduling)

Like tinygrad's scheduler, we fuse operations into kernels.
Elementwise operations can be fused together.
-/

/-- A kernel is a fused set of operations to be executed together. -/
structure Kernel where
  /-- Unique identifier -/
  id : Nat
  /-- Operations in this kernel (in order) -/
  ops : List LazyNode
  /-- Input buffers -/
  inputs : List Nat
  /-- Output buffer -/
  output : Nat
  deriving Repr

/-- Check if an operation can be fused with elementwise ops. -/
def isFusable : LazyNode → Bool
  | .unary _ _ => true
  | .binary _ _ _ => true
  | .const _ _ _ => true
  | _ => false

/-- Simple fusion: group consecutive fusable operations. -/
partial def fuseOperations (nodes : List LazyNode) (nextId : Nat) : List Kernel :=
  match nodes with
  | [] => []
  | n :: rest =>
    if isFusable n then
      -- Collect all fusable ops
      let (fusable, remaining) := rest.span isFusable
      let kernel := {
        id := nextId
        ops := n :: fusable
        inputs := []  -- would extract buffer IDs
        output := nextId
      }
      kernel :: fuseOperations remaining (nextId + 1)
    else
      fuseOperations rest nextId

/-! ## DataArrayN Bridge

Connect LazyTensor to SciLean's DataArrayN for actual computation.
This provides the interface between lazy graphs and concrete execution.
-/

/-- Buffer registry: maps buffer IDs to actual data. -/
structure BufferRegistry where
  nextId : Nat
  /-- We store buffer metadata; actual data is external -/
  shapes : Array (Array Nat)
  dtypes : Array DType
  deriving Repr

namespace BufferRegistry

def empty : BufferRegistry := { nextId := 0, shapes := #[], dtypes := #[] }

def register (reg : BufferRegistry) (shape : Array Nat) (dtype : DType := .float32)
    : (BufferRegistry × Nat) :=
  let id := reg.nextId
  ({ nextId := id + 1
     shapes := reg.shapes.push shape
     dtypes := reg.dtypes.push dtype }, id)

end BufferRegistry

/-- Execution backend trait.

**Status**: Interface only. Implementations should be in separate files:
- `SciLean.Compiler.BLASBackend` for CPU via LeanBLAS
- `SciLean.Compiler.CUDABackend` for GPU (stub exists)
-/
class TensorBackend (B : Type) where
  /-- Allocate a buffer -/
  alloc : B → Array Nat → DType → IO (B × Nat)
  /-- Execute a kernel -/
  execute : B → Kernel → IO Unit
  /-- Synchronize (wait for completion) -/
  sync : B → IO Unit

/-! ## Shape Utilities for DataArrayN Integration -/

/-- Convert concrete shape to symbolic shape. -/
def shapeToSint (shape : Array Nat) : Array Sint :=
  shape.map Sint.nat

/-- Try to evaluate symbolic shape to concrete shape. -/
def sintToShape (shape : Array Sint) : Option (Array Nat) :=
  shape.mapM fun s =>
    match s with
    | .nat n => some n
    | _ => none

/-- Check if two shapes are compatible for broadcasting. -/
def broadcastable (s1 s2 : Array Nat) : Bool :=
  let maxLen := max s1.size s2.size
  let s1' := Array.range maxLen |>.map fun i =>
    s1.getD (s1.size - 1 - (maxLen - 1 - i)) 1
  let s2' := Array.range maxLen |>.map fun i =>
    s2.getD (s2.size - 1 - (maxLen - 1 - i)) 1
  s1'.zip s2' |>.all fun (a, b) => a == b || a == 1 || b == 1

/-- Compute broadcast output shape. -/
def broadcastShape (s1 s2 : Array Nat) : Array Nat :=
  let maxLen := max s1.size s2.size
  Array.range maxLen |>.map fun i =>
    let a := s1.getD (s1.size - 1 - (maxLen - 1 - i)) 1
    let b := s2.getD (s2.size - 1 - (maxLen - 1 - i)) 1
    max a b

/-! ## Interpreter: Execute LazyNode graphs

A simple interpreter that executes LazyNode graphs using FloatArray.
This provides actual computation without needing GPU backends.
-/

/-- Runtime tensor: concrete data with shape. -/
structure RTensor where
  data : FloatArray
  shape : Array Nat
  deriving Inhabited

namespace RTensor

instance : Repr RTensor where
  reprPrec t _ := s!"RTensor({t.shape}, {t.data.size} elems)"

/-- Create a tensor filled with a constant value. -/
def ofConst (value : Float) (shape : Array Nat) : RTensor :=
  let size := shape.foldl (· * ·) 1
  let arr := Id.run do
    let mut arr := FloatArray.emptyWithCapacity size
    for _ in [:size] do
      arr := arr.push value
    return arr
  { data := arr, shape := shape }

/-- Create a tensor from a FloatArray with given shape. -/
def ofArray (data : FloatArray) (shape : Array Nat) : RTensor :=
  { data := data, shape := shape }

/-- Total number of elements. -/
def size (t : RTensor) : Nat := t.shape.foldl (· * ·) 1

/-- Get element at flat index (unchecked). -/
def get (t : RTensor) (i : Nat) : Float := t.data.data[i]!

/-- Set element at flat index (unchecked). -/
def set (t : RTensor) (i : Nat) (v : Float) : RTensor :=
  { t with data := FloatArray.mk (t.data.data.set! i v) }

/-- Compute strides from shape (row-major). Each stride is the product of subsequent dimensions. -/
def computeStrides (shape : Array Nat) : Array Nat :=
  -- stride(n-1) = 1, stride(i) = shape(i+1) * stride(i+1)
  -- Build from right using foldr
  let (strides, _) := shape.foldr (init := (#[], 1)) fun dim (acc, prod) =>
    (acc.push prod, prod * dim)
  strides.reverse

/-- Convert multi-dimensional index to flat index. -/
def flatIndex (shape : Array Nat) (idx : Array Nat) : Nat :=
  let strides := computeStrides shape
  let pairs := idx.zip strides
  pairs.foldl (fun acc (i, s) => acc + i * s) 0

/-- Convert flat index to multi-dimensional index. -/
def unflatIndex (shape : Array Nat) (flat : Nat) : Array Nat :=
  let strides := computeStrides shape
  let (result, _) := strides.foldl (init := (#[], flat)) fun (arr, rem) stride =>
    if stride > 0 then
      (arr.push (rem / stride), rem % stride)
    else
      (arr.push 0, rem)
  result

end RTensor

/-- Buffer storage: maps buffer IDs to runtime tensors (simple assoc list). -/
abbrev BufferStore := List (Nat × RTensor)

namespace BufferStore

def empty : BufferStore := []

def insert (store : BufferStore) (id : Nat) (t : RTensor) : BufferStore :=
  (id, t) :: store.filter (·.1 != id)

def getD (store : BufferStore) (id : Nat) (default : RTensor) : RTensor :=
  match store.find? (·.1 == id) with
  | some (_, t) => t
  | none => default

end BufferStore

/-- Interpreter state. -/
structure InterpState where
  buffers : BufferStore
  deriving Inhabited

namespace Interpreter

/-- Apply a unary operation elementwise. -/
def applyUnary (op : UnaryOp) (x : RTensor) : RTensor :=
  let f : Float → Float := match op with
    | .neg => (- ·)
    | .exp2 => fun v => Float.exp (v * Float.log 2)
    | .log2 => fun v => Float.log v / Float.log 2
    | .sin => Float.sin
    | .sqrt => Float.sqrt
    | .reciprocal => (1.0 / ·)
    | .cast _ => id  -- ignore cast for Float-only interpreter
  let newData := FloatArray.mk (x.data.data.map f)
  { data := newData, shape := x.shape }

/-- Apply a binary operation elementwise (with broadcasting). -/
def applyBinary (op : BinaryOp) (x y : RTensor) : RTensor :=
  let f : Float → Float → Float := match op with
    | .add => (· + ·)
    | .sub => (· - ·)
    | .mul => (· * ·)
    | .div => (· / ·)
    | .max => fun a b => if a >= b then a else b
    | .min => fun a b => if a <= b then a else b
    | .cmpLt => fun a b => if a < b then 1.0 else 0.0
    | .cmpEq => fun a b => if a == b then 1.0 else 0.0
    | .matmul => panic! "matmul should be handled separately"

  -- Simple case: same shape
  if x.shape == y.shape then
    let xArr := x.data.data
    let yArr := y.data.data
    let newData := FloatArray.mk (Array.zipWith f xArr yArr)
    { data := newData, shape := x.shape }
  else
    -- Broadcasting: compute output shape and iterate
    let outShape := broadcastShape x.shape y.shape
    let outSize := outShape.foldl (· * ·) 1
    let result := Id.run do
      let mut result := FloatArray.emptyWithCapacity outSize
      for i in [:outSize] do
        let outIdx := RTensor.unflatIndex outShape i
        -- Map output index to input indices (broadcasting)
        let xIdx := outIdx.mapIdx fun j v =>
          if j < outShape.size - x.shape.size then 0
          else
            let xj := j - (outShape.size - x.shape.size)
            if x.shape.getD xj 1 == 1 then 0 else v
        let yIdx := outIdx.mapIdx fun j v =>
          if j < outShape.size - y.shape.size then 0
          else
            let yj := j - (outShape.size - y.shape.size)
            if y.shape.getD yj 1 == 1 then 0 else v
        let xFlat := RTensor.flatIndex x.shape (xIdx.extract (outShape.size - x.shape.size) outShape.size)
        let yFlat := RTensor.flatIndex y.shape (yIdx.extract (outShape.size - y.shape.size) outShape.size)
        result := result.push (f (x.get xFlat) (y.get yFlat))
      return result
    { data := result, shape := outShape }

/-- Matrix multiplication (2D for now). -/
def matmul (x y : RTensor) : RTensor :=
  -- x: [m, k], y: [k, n] -> [m, n]
  let m := x.shape.getD 0 1
  let k := x.shape.getD 1 1
  let n := y.shape.getD 1 1
  let result := Id.run do
    let mut result := FloatArray.emptyWithCapacity (m * n)
    for i in [:m] do
      for j in [:n] do
        let mut sum : Float := 0.0
        for l in [:k] do
          sum := sum + x.get (i * k + l) * y.get (l * n + j)
        result := result.push sum
    return result
  { data := result, shape := #[m, n] }

/-- Reduce operation along specified axes. -/
def applyReduce (op : ReduceOp) (axes : Array Nat) (x : RTensor) : RTensor :=
  let floatMax (a b : Float) : Float := if a >= b then a else b
  let floatMin (a b : Float) : Float := if a <= b then a else b
  let f : Float → Float → Float := match op with
    | .sum => (· + ·)
    | .max => floatMax
    | .min => floatMin
  let init : Float := match op with
    | .sum => 0.0
    | .max => -1.0e308  -- approximate negative infinity
    | .min => 1.0e308   -- approximate positive infinity

  -- Compute output shape (axes become size 1)
  let outShape := x.shape.mapIdx fun i dim =>
    if axes.contains i then 1 else dim

  -- Initialize result with init values
  let initResult := RTensor.ofConst init outShape

  -- Iterate over input, accumulate into output
  let result := Id.run do
    let mut result := initResult
    for i in [:x.size] do
      let inIdx := RTensor.unflatIndex x.shape i
      let outIdx := inIdx.mapIdx fun j v => if axes.contains j then 0 else v
      let outFlat := RTensor.flatIndex outShape outIdx
      let oldVal := result.get outFlat
      let newVal := f oldVal (x.get i)
      result := result.set outFlat newVal
    return result
  result

/-- Reshape tensor (just changes shape metadata). -/
def reshape (newShape : Array Nat) (x : RTensor) : RTensor :=
  { x with shape := newShape }

/-- Permute tensor dimensions. -/
def permute (perm : Array Nat) (x : RTensor) : RTensor :=
  let newShape := perm.map (x.shape.getD · 1)
  let outSize := newShape.foldl (· * ·) 1
  let result := Id.run do
    let mut result := FloatArray.emptyWithCapacity outSize
    for i in [:outSize] do
      let outIdx := RTensor.unflatIndex newShape i
      -- Inverse permute to get input index
      let inIdx := Array.range x.shape.size |>.map fun j =>
        outIdx.getD (perm.findIdx? (· == j) |>.getD 0) 0
      let inFlat := RTensor.flatIndex x.shape inIdx
      result := result.push (x.get inFlat)
    return result
  { data := result, shape := newShape }

/-- Interpret a LazyNode, returning the computed tensor. -/
partial def interpret (state : InterpState) (node : LazyNode) : RTensor :=
  match node with
  | .buffer id _ _ =>
    state.buffers.getD id (RTensor.ofConst 0.0 #[])

  | .const value shape _ =>
    match sintToShape shape with
    | some s => RTensor.ofConst value s
    | none => panic! "Cannot interpret symbolic shape"

  | .unary op x =>
    let xVal := interpret state x
    applyUnary op xVal

  | .binary .matmul x y =>
    let xVal := interpret state x
    let yVal := interpret state y
    matmul xVal yVal

  | .binary op x y =>
    let xVal := interpret state x
    let yVal := interpret state y
    applyBinary op xVal yVal

  | .reduce op axes x =>
    let xVal := interpret state x
    applyReduce op axes xVal

  | .movement (.reshape newShape) x =>
    let xVal := interpret state x
    match sintToShape newShape with
    | some s => reshape s xVal
    | none => panic! "Cannot interpret symbolic shape"

  | .movement (.permute perm) x =>
    let xVal := interpret state x
    permute perm xVal

  | .movement (.expand _) x =>
    -- Expand is handled by broadcasting in binary ops
    interpret state x

  | .movement (.pad _) _ =>
    panic! "pad not yet implemented"

  | .movement (.shrink _) _ =>
    panic! "shrink not yet implemented"

  | .movement (.flip _) _ =>
    panic! "flip not yet implemented"

end Interpreter

/-- Execute a lazy tensor and get the result. -/
def LazyTensor.run (buffers : BufferStore := []) (t : LazyTensor) : RTensor :=
  let node := t.realize  -- Apply simplification rules first
  Interpreter.interpret { buffers := buffers } node

/-- Execute a lazy tensor with a list of input buffers. -/
def LazyTensor.runWithInputs (inputs : List (Nat × RTensor)) (t : LazyTensor) : RTensor :=
  let buffers := inputs.foldl (fun m (id, tensor) => m.insert id tensor) BufferStore.empty
  t.run buffers

/-- Create a lazy tensor from a runtime tensor. -/
def LazyTensor.ofRTensor (id : Nat) (t : RTensor) : LazyTensor × BufferStore :=
  let lt := LazyTensor.fromBuffer id (shapeToSint t.shape)
  let store : BufferStore := BufferStore.empty.insert id t
  (lt, store)

/-! ## Convenience functions for testing -/

/-- Create a tensor from a list of floats with given shape. -/
def RTensor.ofList (data : List Float) (shape : Array Nat) : RTensor :=
  { data := data.toFloatArray, shape := shape }

/-- Pretty print a tensor. -/
def RTensor.toString (t : RTensor) : String :=
  let shapeStr := t.shape.toList.map ToString.toString |> String.intercalate "×"
  let dataStr := t.data.toList.take 10 |>.map (Float.toString) |> String.intercalate ", "
  let suffix := if t.size > 10 then ", ..." else ""
  s!"RTensor[{shapeStr}]({dataStr}{suffix})"

instance : ToString RTensor := ⟨RTensor.toString⟩

end SciLean.Compiler
