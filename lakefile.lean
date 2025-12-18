
import Lake
open Lake DSL System

def linkArgs :=
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    -- Apple Silicon uses /opt/homebrew, Intel uses /usr/local
    -- Only include paths that exist to avoid linker warnings
    #["-L/opt/homebrew/opt/openblas/lib", "-lblas"]
  else -- assuming linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]

-- Metal framework linking for final executables only
-- Need to specify the SDK sysroot for lld to find frameworks and libobjc
def metalLinkArgs :=
  if System.Platform.isOSX then
    #["-Wl,-syslibroot,/Applications/Xcode-26.1.1.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk",
      "-lobjc",
      "-framework", "Metal", "-framework", "Foundation", "-framework", "CoreFoundation",
      "-framework", "MetalPerformanceShaders", "-framework", "Accelerate"]
  else
    #[]
def inclArgs :=
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    #["-I/opt/homebrew/opt/openblas/include"]
  else -- assuming linux
    #[]


package scilean {
  -- Global link args should be minimal; Metal frameworks are added per-executable.
  moreLinkArgs := linkArgs
  -- leanOptions := #[⟨`doc.verso, true⟩]  -- disabled for now
}


-- Use latest mathlib (includes compile_inductive fix PR #32225)
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

-- Use local LeanBLAS
require leanblas from ".." / "LeanBLAS"

-- LeanPlot for visualization (local dependency)
require leanplot from ".." / "LeanPlot"

-- SorryProof for type-safe sorry macros (local dependency)
require sorryproof from ".." / "SorryProof"

-- Link LeanBLAS's C FFI library into SciLean executables.
--
-- The BLAS bindings come from the `leanblas` package and require its native
-- static library (`libleanblasc.a` / `libleanblasc.lib`) at link time.
--
-- Unfortunately, Lake currently does not propagate the output type/kind of
-- custom targets across package boundaries, so we cannot directly reference the
-- dependency's custom target as a `Target FilePath` here.
--
-- Instead, we define a local target that *depends* on `leanblas/libleanblasc`
-- but returns the known output path. This keeps the build graph correct and
-- makes executables link successfully.
target libleanblasc : FilePath := do
  let ws ← getWorkspace
  let some leanblasPkg := ws.findPackage? `leanblas
    | error "SciLean: dependency package `leanblas` not found in workspace."
  let depJob : Job (CustomData `leanblas `libleanblasc) ← fetch <| leanblasPkg.target `libleanblasc
  let libPath := leanblasPkg.sharedLibDir / nameToStaticLib "leanblasc"
  depJob.mapM (sync := true) fun _ => pure libPath


-- Extra C compiler flags for macOS
--
-- SciLean links against OpenBLAS by default, so we intentionally avoid
-- Accelerate-only flags such as `-DACCELERATE_NEW_LAPACK`.
def cFlagsOSX :=
  (#[] : Array String)

-- FFI - build all `*.c` files in `./C` directory and package them into `libscileanc.a/so` library
target libscileanc pkg : FilePath := do
  let mut oFiles : Array (Job FilePath) := #[]
  for file in (← (pkg.dir / "C").readDir) do
    if file.path.extension == some "c" then
      let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
      let srcJob ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ inclArgs
      let cFlags := #["-fPIC", "-O3", "-DNDEBUG"] ++ cFlagsOSX
      oFiles := oFiles.push (← buildO oFile srcJob weakArgs cFlags "gcc" getLeanTrace)
  let name := nameToStaticLib "scileanc"
  buildStaticLib (pkg.sharedLibDir / name) oFiles

-- Metal backend (macOS only)
target libscileanmetal pkg : FilePath := do
  let mut oFiles : Array (Job FilePath) := #[]
  if System.Platform.isOSX then
    -- Build Objective-C++ wrapper
    let mmSrc := pkg.dir / "Metal" / "metal_backend.mm"
    let mmObj := pkg.buildDir / "metal" / "metal_backend.o"
    let srcJob ← inputTextFile mmSrc
    let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-fobjc-arc"]
    oFiles := oFiles.push (← buildO mmObj srcJob weakArgs #["-fPIC", "-O3", "-DNDEBUG", "-std=c++17"] "clang++" getLeanTrace)
  let name := nameToStaticLib "scileanmetal"
  buildStaticLib (pkg.sharedLibDir / name) oFiles


@[default_target]
lean_lib SciLean {
  roots := #[`SciLean]
  -- On macOS with Lean 4.26.0-rc2, Mathlib's shared library fails to link
  -- due to an upstream lld duplicate-symbol issue. Disabling precompilation
  -- avoids requiring `Mathlib:shared` during development.
  precompileModules := if System.Platform.isOSX then false else true
}

-- C-based FFI modules (precompiled for editor support)
lean_lib SciLean.FFI.Core where
  roots := #[`SciLean.FFI.ByteArray, `SciLean.FFI.FloatArray, `SciLean.FFI.Float, `SciLean.FFI.Float32Array, `SciLean.FFI.BLAS]
  precompileModules := if System.Platform.isOSX then false else true
  moreLinkObjs := #[libscileanc, libleanblasc]

-- Kernel: dtype-parametric tensor operations (minimal C kernel)
lean_lib SciLean.Kernel where
  roots := #[`SciLean.Kernel.DType, `SciLean.Kernel.Ops, `SciLean.Kernel.Spec, `SciLean.Kernel.Axioms, `SciLean.Kernel.AD, `SciLean.Kernel.Integration]
  precompileModules := if System.Platform.isOSX then false else true
  moreLinkObjs := #[libscileanc]

-- Metal backend (not precompiled - linked at executable time)
lean_lib SciLean.FFI.Metal where
  roots := #[`SciLean.FFI.Metal]
  precompileModules := false
  moreLinkObjs := #[libscileanmetal]


@[test_driver]
lean_lib SciLeanTest {
  -- Many tests currently rely on `#eval`/FFI and/or very large reductions.
  -- On macOS we disable module precompilation (to avoid `Mathlib:shared`),
  -- which makes those tests incompatible with the interpreter.
  --
  -- So on macOS we run a lightweight "smoke" test module. On other platforms
  -- we keep building the full test suite.
  srcDir := "test"
  roots := if System.Platform.isOSX then #[`Smoke] else #[]
  globs := if System.Platform.isOSX then #[] else #[Glob.submodules `SciLeanTest]
}




----------------------------------------------------------------------------------------------------
lean_exe Doodle {
  root := `examples.Doodle
}

lean_exe WaveEquation {
  root := `examples.WaveEquation
}

lean_exe HelloWorld {
  root := `examples.HelloWorld
}


lean_exe HarmonicOscillator {
  root := `examples.HarmonicOscillator
}

lean_exe CircleOptimisation {
  root := `examples.CircleOptimisation
}

lean_exe Ballistic {
  root := `examples.Ballistic
}

lean_exe ComputeBackendTest {
  root := `examples.ComputeBackendTest
  moreLinkArgs := metalLinkArgs
}

lean_exe BackendBenchmark {
  root := `examples.BackendBenchmark
  moreLinkArgs := metalLinkArgs
}

lean_exe WalkOnSpheres {
  root := `examples.WalkOnSpheres
}

lean_exe BFGS {
  root := `Test.optimjl.bfgs
}

lean_exe LBFGS {
  root := `Test.optimjl.lbfgs
}

lean_exe GMM {
  root := `SciLean.Examples.GMM.Main
}

lean_exe BlasTest {
  root := `examples.BlasTest
}

lean_exe FloatTest {
  root := `examples.FloatTest
}

lean_exe ForLoopTest {
  buildType := .release
  moreLinkArgs := #["-O3", "-UNDEBUG"]
  root := `tests.sum_speed_test
}

lean_exe SurfaceMeshTests {
  root := `examples.SurfaceMeshTests
}

lean_exe FloatMatrixTest {
  root := `examples.FloatMatrixTest
}


lean_exe ProfileKMeans {
  root := `examples.Profile.KMeans
}
lean_exe ProfileKMeansDirection {
  root := `examples.Profile.KMeansDirection
}

lean_exe ProfileTensorOps {
  root := `examples.Profile.TensorOps
}

lean_exe ProfileGMM {
  root := `examples.Profile.GMM
}

lean_exe ProfileLSTM {
  root := `examples.Profile.LSTM
}


lean_exe MNISTClassifier where
  root := `examples.MNISTClassifier

lean_exe MetalBenchmark where
  root := `examples.MetalBenchmark
  moreLinkArgs := metalLinkArgs

lean_exe GEMMBenchmark where
  root := `examples.GEMMBenchmark

lean_exe KernelGEMMBenchmark where
  buildType := .release
  root := `examples.KernelGEMMBenchmark

lean_exe SimpleMNIST where
  root := `examples.SimpleMNIST

-- LeanBLAS FFI library path for local dependency
def leanblasLibPath : FilePath := ".." / "LeanBLAS" / ".lake" / "build" / "lib"

lean_exe DependentMNIST where
  root := `examples.DependentMNIST
  -- Explicitly link LeanBLAS FFI for local path dependency
  moreLinkArgs := #["-L" ++ leanblasLibPath.toString, "-lleanblasc"]

lean_exe TestMinimal where
  root := `examples.TestMinimal

lean_exe TestNpyRoundtrip where
  root := `examples.TestNpyRoundtrip
  moreLinkArgs := #["-L" ++ leanblasLibPath.toString, "-lleanblasc"]

lean_exe VerifyPyTorchMNIST where
  root := `examples.VerifyPyTorchMNIST
  moreLinkArgs := #["-L" ++ leanblasLibPath.toString, "-lleanblasc"]

lean_exe Float32Benchmark where
  root := `examples.Float32Benchmark
  moreLinkArgs := metalLinkArgs

lean_exe Numpy100 where
  root := `examples.Numpy100
  -- LeanBLAS needs explicit linking for local path dependency
  moreLinkArgs := #["-L" ++ leanblasLibPath.toString, "-lleanblasc"]

lean_exe RandBenchmark where
  buildType := .release
  moreLinkArgs := #["-O3", "-UNDEBUG"]
  root := `examples.RandBenchmark

lean_exe OverheadTest where
  root := `examples.OverheadTest
  moreLinkArgs := metalLinkArgs

lean_exe LargeGEMM where
  root := `examples.LargeGEMM
  moreLinkArgs := metalLinkArgs

lean_exe MetalMinimalBenchmark where
  root := `examples.MetalMinimalBenchmark
  moreLinkArgs := metalLinkArgs

lean_exe Conv2DTest where
  root := `examples.Conv2DTest
  moreLinkArgs := metalLinkArgs

lean_exe GEMMComparison where
  root := `examples.GEMMComparison
  moreLinkArgs := metalLinkArgs

lean_exe GEMMFocus where
  root := `examples.GEMMFocus
  moreLinkArgs := metalLinkArgs

lean_exe GEMMCorrectness where
  root := `examples.GEMMCorrectness
  moreLinkArgs := metalLinkArgs

lean_exe AttentionTest where
  root := `examples.AttentionTest
  moreLinkArgs := metalLinkArgs

lean_exe GpuBufferBenchmark where
  root := `examples.GpuBufferBenchmark
  moreLinkArgs := metalLinkArgs

lean_exe KernelTest where
  root := `examples.KernelTest

lean_exe IntegrationTest where
  root := `examples.IntegrationTest

lean_exe KernelBenchmark where
  buildType := .release
  root := `examples.KernelBenchmark

lean_exe GemmGen where
  root := `codegen.GemmGen

lean_exe MetalShaderGen where
  root := `codegen.MetalShaderGen

lean_exe GpuFusedKernelTest where
  root := `test.gpu_fused_kernels
  moreLinkArgs := metalLinkArgs

lean_exe GpuBatchingBenchmark where
  buildType := .release
  root := `examples.GpuBatchingBenchmark
  moreLinkArgs := metalLinkArgs

lean_exe GpuMNIST where
  root := `examples.GpuMNIST
  moreLinkArgs := metalLinkArgs
