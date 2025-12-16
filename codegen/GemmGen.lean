/-!
# GEMM Code Generator

Generates optimized C code for GEMM with tunable parameters.
Target: NEON on Apple Silicon (ARM64)
-/

namespace GemmGen

structure Config where
  mr : Nat := 4        -- Micro-kernel rows
  nr : Nat := 4        -- Micro-kernel cols (must be multiple of 4 for NEON)
  kUnroll : Nat := 4   -- K-loop unroll factor
  tileM : Nat := 64
  tileN : Nat := 64
  tileK : Nat := 64
  deriving Repr

def brace (s : String) : String := "{" ++ s ++ "}"

/-- Generate NEON accumulator declarations -/
def genAccumulatorDecls (mr nr : Nat) : String := Id.run do
  let mut s := ""
  for i in List.range mr do
    for j in List.range (nr/4) do
      s := s ++ s!"    float32x4_t c{i}_{j} = vdupq_n_f32(0.0f);\n"
  return s

/-- Generate the inner K-loop body for one K iteration -/
def genKLoopBody (mr nr : Nat) (kOffset : String) (suffix : String := "") (prefetchDist : Nat := 0) : String := Id.run do
  let mut s := ""

  -- Prefetch ahead for next K iteration if requested
  if prefetchDist > 0 then
    s := s ++ s!"        __builtin_prefetch(&B[({kOffset} + {prefetchDist}) * ldb], 0, 3);\n"

  -- Load A column (mr elements, gathered from mr rows)
  -- Note: kOffset may be an expression like "kk + 1", so wrap in parens for correct precedence
  if mr == 4 then
    s := s ++ s!"        float32x4_t a_col{suffix} = " ++ brace s!"A[0*lda + ({kOffset})], A[1*lda + ({kOffset})], A[2*lda + ({kOffset})], A[3*lda + ({kOffset})]" ++ ";\n"
  else if mr == 8 then
    s := s ++ s!"        float32x4_t a0_{suffix} = " ++ brace s!"A[0*lda + ({kOffset})], A[1*lda + ({kOffset})], A[2*lda + ({kOffset})], A[3*lda + ({kOffset})]" ++ ";\n"
    s := s ++ s!"        float32x4_t a1_{suffix} = " ++ brace s!"A[4*lda + ({kOffset})], A[5*lda + ({kOffset})], A[6*lda + ({kOffset})], A[7*lda + ({kOffset})]" ++ ";\n"

  -- Load B row(s) (nr elements, contiguous)
  -- CRITICAL: Wrap kOffset in parens - "kk + 1 * ldb" != "(kk + 1) * ldb"
  for j in List.range (nr/4) do
    s := s ++ s!"        float32x4_t b{j}_{suffix} = vld1q_f32(&B[({kOffset}) * ldb + {j*4}]);\n"

  -- FMA operations
  if mr == 4 then
    for j in List.range (nr/4) do
      for i in List.range 4 do
        s := s ++ s!"        c{i}_{j} = vmlaq_laneq_f32(c{i}_{j}, b{j}_{suffix}, a_col{suffix}, {i});\n"
  else if mr == 8 then
    for j in List.range (nr/4) do
      for i in List.range 4 do
        s := s ++ s!"        c{i}_{j} = vmlaq_laneq_f32(c{i}_{j}, b{j}_{suffix}, a0_{suffix}, {i});\n"
      for i in List.range 4 do
        s := s ++ s!"        c{i+4}_{j} = vmlaq_laneq_f32(c{i+4}_{j}, b{j}_{suffix}, a1_{suffix}, {i});\n"

  return s

/-- Generate K-loop with unrolling -/
def genKLoop (mr nr kUnroll : Nat) : String := Id.run do
  let mut s := ""
  s := s ++ "    size_t kk = 0;\n"

  if kUnroll > 1 then
    s := s ++ s!"    for (; kk + {kUnroll} <= K; kk += {kUnroll}) " ++ "{\n"
    for u in List.range kUnroll do
      s := s ++ genKLoopBody mr nr s!"kk + {u}" s!"u{u}"
    s := s ++ "    }\n"
    s := s ++ "    for (; kk < K; kk++) {\n"
    s := s ++ genKLoopBody mr nr "kk" "r"
    s := s ++ "    }\n"
  else
    s := s ++ "    for (; kk < K; kk++) {\n"
    s := s ++ genKLoopBody mr nr "kk" ""
    s := s ++ "    }\n"

  return s

/-- Generate store-back code -/
def genStoreBack (mr nr : Nat) : String := Id.run do
  let mut s := ""
  for i in List.range mr do
    for j in List.range (nr/4) do
      s := s ++ s!"    vst1q_f32(&C[{i}*ldc + {j*4}], vaddq_f32(vld1q_f32(&C[{i}*ldc + {j*4}]), c{i}_{j}));\n"
  return s

/-- Config name for unique function naming -/
def Config.name (cfg : Config) : String :=
  s!"{cfg.mr}x{cfg.nr}_k{cfg.kUnroll}_t{cfg.tileM}"

/-- Generate the micro-kernel function -/
def genMicroKernel (cfg : Config) : String :=
  let header := s!"
/* Generated NEON micro-kernel: {cfg.mr}x{cfg.nr}, K-unroll={cfg.kUnroll} */
__attribute__((always_inline))
static inline void gemm_microkernel_{cfg.name}_neon(
    float* __restrict__ C, size_t ldc,
    const float* __restrict__ A, size_t lda,
    const float* __restrict__ B, size_t ldb,
    size_t K)
"
  let body := "{\n" ++
    genAccumulatorDecls cfg.mr cfg.nr ++
    genKLoop cfg.mr cfg.nr cfg.kUnroll ++
    genStoreBack cfg.mr cfg.nr ++
    "}\n"
  header ++ body

/-- Generate tiled GEMM -/
def genTiledGemm (cfg : Config) : String :=
  let lb := "{"
  let rb := "}"
s!"
/* Generated tiled GEMM: MR={cfg.mr}, NR={cfg.nr}, tiles={cfg.tileM}x{cfg.tileN}x{cfg.tileK} */
__attribute__((always_inline))
static inline void gemm_f32_gen_{cfg.name}(
    float* __restrict__ C,
    const float* __restrict__ A,
    const float* __restrict__ B,
    size_t M, size_t K, size_t N,
    float alpha, float beta)
{lb}
    if (beta != 1.0f) {lb}
        for (size_t i = 0; i < M * N; i++) {lb}
            C[i] *= beta;
        {rb}
    {rb}

    for (size_t i0 = 0; i0 < M; i0 += {cfg.tileM}) {lb}
        size_t i_end = (i0 + {cfg.tileM} < M) ? i0 + {cfg.tileM} : M;

        for (size_t j0 = 0; j0 < N; j0 += {cfg.tileN}) {lb}
            size_t j_end = (j0 + {cfg.tileN} < N) ? j0 + {cfg.tileN} : N;

            for (size_t k0 = 0; k0 < K; k0 += {cfg.tileK}) {lb}
                size_t k_end = (k0 + {cfg.tileK} < K) ? k0 + {cfg.tileK} : K;
                size_t tile_k = k_end - k0;

                size_t i;
                for (i = i0; i + {cfg.mr} <= i_end; i += {cfg.mr}) {lb}
                    size_t j;
                    for (j = j0; j + {cfg.nr} <= j_end; j += {cfg.nr}) {lb}
                        gemm_microkernel_{cfg.name}_neon(
                            &C[i * N + j], N,
                            &A[i * K + k0], K,
                            &B[k0 * N + j], N,
                            tile_k);
                    {rb}
                    for (; j < j_end; j++) {lb}
                        for (size_t ii = i; ii < i + {cfg.mr}; ii++) {lb}
                            float sum = 0.0f;
                            for (size_t kk = k0; kk < k_end; kk++) {lb}
                                sum += A[ii * K + kk] * B[kk * N + j];
                            {rb}
                            C[ii * N + j] += sum;
                        {rb}
                    {rb}
                {rb}
                for (; i < i_end; i++) {lb}
                    for (size_t j = j0; j < j_end; j++) {lb}
                        float sum = 0.0f;
                        for (size_t kk = k0; kk < k_end; kk++) {lb}
                            sum += A[i * K + kk] * B[kk * N + j];
                        {rb}
                        C[i * N + j] += sum;
                    {rb}
                {rb}
            {rb}
        {rb}
    {rb}

    if (alpha != 1.0f) {lb}
        for (size_t i = 0; i < M * N; i++) {lb}
            C[i] *= alpha;
        {rb}
    {rb}
{rb}
"

/-- Generate complete kernel file -/
def genKernelFile (configs : List Config) : String := Id.run do
  let mut s := "/* Auto-generated GEMM kernels - DO NOT EDIT */\n"
  s := s ++ "#pragma once\n\n"
  s := s ++ "#include <arm_neon.h>\n"
  s := s ++ "#include <stddef.h>\n\n"

  for cfg in configs do
    s := s ++ genMicroKernel cfg
    s := s ++ "\n"
    s := s ++ genTiledGemm cfg
    s := s ++ "\n"

  return s

/-- Configurations to generate -/
def configs : List Config := [
  -- Baseline
  { mr := 4, nr := 4, kUnroll := 1, tileM := 64, tileN := 64, tileK := 64 },
  -- 8x8 with different K-unroll factors
  { mr := 8, nr := 8, kUnroll := 2, tileM := 128, tileN := 128, tileK := 128 },
  { mr := 8, nr := 8, kUnroll := 4, tileM := 128, tileN := 128, tileK := 128 },
  { mr := 8, nr := 8, kUnroll := 8, tileM := 128, tileN := 128, tileK := 128 },
  -- Try different tile sizes with best micro-kernel
  { mr := 8, nr := 8, kUnroll := 4, tileM := 64, tileN := 64, tileK := 256 },
  { mr := 8, nr := 8, kUnroll := 4, tileM := 256, tileN := 256, tileK := 64 }
]

end GemmGen

def main : IO Unit := do
  IO.println (GemmGen.genKernelFile GemmGen.configs)
