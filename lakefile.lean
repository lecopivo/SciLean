
import Lake
open Lake DSL System

def linkArgs :=
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    #["-L/opt/homebrew/opt/openblas/lib",
      "-L/usr/local/opt/openblas/lib", "-lblas"]
  else -- assuming linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]

-- Metal framework linking for final executables only
-- Need to specify the SDK sysroot for lld to find frameworks and libobjc
def metalLinkArgs :=
  if System.Platform.isOSX then
    #["-Wl,-syslibroot,/Applications/Xcode-26.1.1.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk",
      "-lobjc",
      "-framework", "Metal", "-framework", "Foundation", "-framework", "CoreFoundation"]
  else
    #[]
def inclArgs :=
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    #["-I/opt/homebrew/opt/openblas/include",
      "-I/usr/local/opt/openblas/include"]
  else -- assuming linux
    #[]


package scilean {
  moreLinkArgs := linkArgs
  leanOptions := #[⟨`doc.verso, true⟩]
}


-- Use latest mathlib (includes compile_inductive fix PR #32225)
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

-- Use local LeanBLAS
require leanblas from ".." / "LeanBLAS"

-- LeanPlot for visualization (local dependency)
require leanplot from ".." / "LeanPlot"


-- FFI - build all `*.c` files in `./C` directory and package them into `libscileanc.a/so` library
target libscileanc pkg : FilePath := do
  let mut oFiles : Array (Job FilePath) := #[]
  for file in (← (pkg.dir / "C").readDir) do
    if file.path.extension == some "c" then
      let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
      let srcJob ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString]
      oFiles := oFiles.push (← buildO oFile srcJob weakArgs #["-fPIC", "-O3", "-DNDEBUG"] "gcc" getLeanTrace)
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
}

-- C-based FFI modules (precompiled for editor support)
lean_lib SciLean.FFI.Core where
  roots := #[`SciLean.FFI.ByteArray, `SciLean.FFI.FloatArray, `SciLean.FFI.Float, `SciLean.FFI.BLAS]
  precompileModules := true
  moreLinkObjs := #[libscileanc]

-- Metal backend (not precompiled - linked at executable time)
lean_lib SciLean.FFI.Metal where
  roots := #[`SciLean.FFI.Metal]
  precompileModules := false
  moreLinkObjs := #[libscileanmetal]


@[test_driver]
lean_lib Test {
  globs := #[Glob.submodules `Test]
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
