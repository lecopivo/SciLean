
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
}                               --


-- require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.19.0"
require leanblas from git "https://github.com/lecopivo/LeanBLAS" @ "v4.20.1"


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


@[default_target]
lean_lib SciLean {
  roots := #[`SciLean]
}

-- Files that should be compiled, either to get fast tactic or to make FFI functions work in editor
lean_lib SciLean.FFI where
  precompileModules := true
  moreLinkObjs := #[libscileanc]


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
