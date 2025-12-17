/-!
# Metal Shader Code Generator

Generates Metal shader code for GPU compute kernels from Lean specifications.
Supports element-wise unary/binary ops and simple fusions.
-/

namespace MetalShaderGen

/-- A Metal type representation -/
inductive MetalType
  | float32
  | float16
  | int32
  | uint32
  | bool
  deriving Repr, BEq

def MetalType.toString : MetalType → String
  | .float32 => "float"
  | .float16 => "half"
  | .int32 => "int"
  | .uint32 => "uint"
  | .bool => "bool"

/-- An expression in the Metal shader language -/
inductive Expr
  | var (name : String)
  | lit (value : Float)
  | litInt (value : Int)
  | call (fn : String) (args : List Expr)
  | binop (op : String) (lhs rhs : Expr)
  | unop (op : String) (arg : Expr)
  | ternary (cond thenExpr elseExpr : Expr)
  | index (arr : String) (idx : Expr)
  deriving Repr

partial def Expr.render : Expr → String
  | .var name => name
  | .lit v => s!"{v}f"
  | .litInt v => s!"{v}"
  | .call fn args => s!"{fn}({String.intercalate ", " (args.map render)})"
  | .binop op lhs rhs => s!"({lhs.render} {op} {rhs.render})"
  | .unop op arg => s!"{op}({arg.render})"
  | .ternary c t e => s!"({c.render} ? {t.render} : {e.render})"
  | .index arr idx => s!"{arr}[{idx.render}]"

/-- Specification of a unary element-wise operation -/
structure UnaryOp where
  name : String
  body : Expr  -- Expression using "x" as input variable
  deriving Repr

/-- Specification of a binary element-wise operation -/
structure BinaryOp where
  name : String
  body : Expr  -- Expression using "a" and "b" as input variables
  deriving Repr

/-- Generate a unary element-wise kernel -/
def genUnaryKernel (op : UnaryOp) : String :=
  let body := op.body.render
  s!"kernel void {op.name}(
    device const float* input [[buffer(0)]],
    device float* output [[buffer(1)]],
    uint id [[thread_position_in_grid]]
) \{
    float x = input[id];
    output[id] = {body};
}
"

/-- Generate a binary element-wise kernel -/
def genBinaryKernel (op : BinaryOp) : String :=
  let body := op.body.render
  s!"kernel void {op.name}(
    device const float* a_arr [[buffer(0)]],
    device const float* b_arr [[buffer(1)]],
    device float* output [[buffer(2)]],
    uint id [[thread_position_in_grid]]
) \{
    float a = a_arr[id];
    float b = b_arr[id];
    output[id] = {body};
}
"

/-- Generate a fused kernel from a sequence of operations -/
structure FusedOp where
  name : String
  inputs : List String       -- Input buffer names
  /-- Operations as (result_var, expression) pairs -/
  steps : List (String × Expr)
  output : Expr
  deriving Repr

def genFusedKernel (op : FusedOp) : String := Id.run do
  let mut bufferDecls := ""
  let mut idx : Nat := 0
  for input in op.inputs do
    bufferDecls := bufferDecls ++ s!"    device const float* {input} [[buffer({idx})]],\n"
    idx := idx + 1

  let outputIdx := op.inputs.length
  bufferDecls := bufferDecls ++ s!"    device float* output [[buffer({outputIdx})]],\n"
  bufferDecls := bufferDecls ++ "    uint id [[thread_position_in_grid]]"

  let mut bodySteps := ""
  for (varName, expr) in op.steps do
    bodySteps := bodySteps ++ s!"    float {varName} = {expr.render};\n"

  s!"kernel void {op.name}(
{bufferDecls}
) \{
{bodySteps}    output[id] = {op.output.render};
}
"

/-- Helper functions for building expressions -/
def x : Expr := .var "x"
def a : Expr := .var "a"
def b : Expr := .var "b"
def idx : Expr := .var "id"

def call1 (fn : String) (arg : Expr) : Expr := .call fn [arg]
def call2 (fn : String) (a b : Expr) : Expr := .call fn [a, b]
def add (a b : Expr) : Expr := .binop "+" a b
def sub (a b : Expr) : Expr := .binop "-" a b
def mul (a b : Expr) : Expr := .binop "*" a b
def div (a b : Expr) : Expr := .binop "/" a b
def neg (e : Expr) : Expr := .unop "-" e
def max' (a b : Expr) : Expr := call2 "max" a b
def min' (a b : Expr) : Expr := call2 "min" a b

-- Standard library functions
def exp' (e : Expr) : Expr := call1 "exp" e
def log' (e : Expr) : Expr := call1 "log" e
def sqrt' (e : Expr) : Expr := call1 "sqrt" e
def sin' (e : Expr) : Expr := call1 "sin" e
def cos' (e : Expr) : Expr := call1 "cos" e
def tanh' (e : Expr) : Expr := call1 "tanh" e
def abs' (e : Expr) : Expr := call1 "abs" e
def erf' (e : Expr) : Expr := call1 "erf" e
def pow' (base exp : Expr) : Expr := call2 "pow" base exp
def rsqrt' (e : Expr) : Expr := call1 "rsqrt" e

/-- Standard unary operations -/
def standardUnaryOps : List UnaryOp := [
  { name := "neg_gen", body := neg x },
  { name := "exp_gen", body := exp' x },
  { name := "log_gen", body := log' x },
  { name := "sqrt_gen", body := sqrt' x },
  { name := "sin_gen", body := sin' x },
  { name := "cos_gen", body := cos' x },
  { name := "tanh_gen", body := tanh' x },
  { name := "abs_gen", body := abs' x },
  { name := "reciprocal_gen", body := div (.lit 1.0) x },
  { name := "rsqrt_gen", body := rsqrt' x },
  -- ReLU: max(0, x)
  { name := "relu_gen", body := max' (.lit 0.0) x },
  -- Sigmoid: 1 / (1 + exp(-x))
  { name := "sigmoid_gen", body := div (.lit 1.0) (add (.lit 1.0) (exp' (neg x))) },
  -- SiLU/Swish: x * sigmoid(x) = x / (1 + exp(-x))
  { name := "silu_gen", body := div x (add (.lit 1.0) (exp' (neg x))) },
  -- Softplus: log(1 + exp(x))
  { name := "softplus_gen", body := log' (add (.lit 1.0) (exp' x)) },
  -- GELU approximation: 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
  { name := "gelu_gen", body :=
      let sqrt2pi := Expr.lit 0.7978845608  -- sqrt(2/pi)
      let c := Expr.lit 0.044715
      let x3 := mul x (mul x x)
      mul (mul (.lit 0.5) x)
          (add (.lit 1.0) (tanh' (mul sqrt2pi (add x (mul c x3))))) },
  -- LeakyReLU: max(0.01*x, x)
  { name := "leaky_relu_gen", body := max' (mul (.lit 0.01) x) x },
  -- ELU: x if x > 0 else exp(x) - 1
  { name := "elu_gen", body :=
      .ternary (.binop ">" x (.lit 0.0)) x (sub (exp' x) (.lit 1.0)) },
  -- Hardswish: x * min(max(0, x+3), 6) / 6
  { name := "hardswish_gen", body :=
      mul x (div (min' (max' (.lit 0.0) (add x (.lit 3.0))) (.lit 6.0)) (.lit 6.0)) }
]

/-- Standard binary operations -/
def standardBinaryOps : List BinaryOp := [
  { name := "add_gen", body := add a b },
  { name := "sub_gen", body := sub a b },
  { name := "mul_gen", body := mul a b },
  { name := "div_gen", body := div a b },
  { name := "max_gen", body := max' a b },
  { name := "min_gen", body := min' a b },
  { name := "pow_gen", body := pow' a b }
]

/-- Example fused operations -/
def exampleFusedOps : List FusedOp := [
  -- mul_add: a * b + c
  { name := "mul_add_gen",
    inputs := ["a_arr", "b_arr", "c_arr"],
    steps := [
      ("a", .index "a_arr" idx),
      ("b", .index "b_arr" idx),
      ("c", .index "c_arr" idx),
      ("ab", mul (.var "a") (.var "b"))
    ],
    output := add (.var "ab") (.var "c") },
  -- relu_add: relu(a) + b
  { name := "relu_add_gen",
    inputs := ["a_arr", "b_arr"],
    steps := [
      ("a", .index "a_arr" idx),
      ("b", .index "b_arr" idx),
      ("relu_a", max' (.lit 0.0) (.var "a"))
    ],
    output := add (.var "relu_a") (.var "b") },
  -- sigmoid_mul: sigmoid(a) * b
  { name := "sigmoid_mul_gen",
    inputs := ["a_arr", "b_arr"],
    steps := [
      ("a", .index "a_arr" idx),
      ("b", .index "b_arr" idx),
      ("sig", div (.lit 1.0) (add (.lit 1.0) (exp' (neg (.var "a")))))
    ],
    output := mul (.var "sig") (.var "b") }
]

/-- Generate header with includes -/
def genHeader : String :=
  "#include <metal_stdlib>\nusing namespace metal;\n\n// Auto-generated kernels - DO NOT EDIT\n\n"

/-- Generate all standard kernels -/
def genAllKernels : String := Id.run do
  let mut s := genHeader
  s := s ++ "// ============ Unary Element-wise Operations ============\n\n"
  for op in standardUnaryOps do
    s := s ++ genUnaryKernel op ++ "\n"

  s := s ++ "// ============ Binary Element-wise Operations ============\n\n"
  for op in standardBinaryOps do
    s := s ++ genBinaryKernel op ++ "\n"

  s := s ++ "// ============ Fused Operations ============\n\n"
  for op in exampleFusedOps do
    s := s ++ genFusedKernel op ++ "\n"

  return s

end MetalShaderGen

def main : IO Unit := do
  IO.println MetalShaderGen.genAllKernels
