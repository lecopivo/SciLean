
import Lake
open Lake DSL System

package scilean

def moreLinkArgs : Array String := #["-lm", "-L/usr/lib/x86_64-linux-gnu","-lblas"]

@[default_target]
lean_lib SciLean {
  -- precompileModules := true
  roots := #[`SciLean]
  moreLinkArgs := moreLinkArgs
}

@[test_driver]
lean_lib Test {
  globs := #[Glob.submodules `Test]
  moreLinkArgs := moreLinkArgs
}

lean_lib CompileTactics where
  -- options for SciLean.Tactic.MySimpProc (and below) modules
  precompileModules := true
  roots := #[`SciLean.Tactic.LSimp.LetNormalize,
             `SciLean.Tactic.CompiledTactics,
             `SciLean.Data.Float,
             `SciLean.Data.FloatArray]
  moreLinkArgs := moreLinkArgs


extern_lib libscileanc pkg := do
  let mut oFiles : Array (Job FilePath) := #[]
  for file in (← (pkg.dir / "C").readDir) do
    if file.path.extension == some "c" then
      let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
      let srcJob ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString]
      oFiles := oFiles.push (← buildO oFile srcJob weakArgs #["-fPIC"] "gcc" getLeanTrace)
  let name := nameToStaticLib "scileanc"
  buildStaticLib (pkg.nativeLibDir / name) oFiles


lean_exe Doodle {
  root := `examples.Doodle
}

lean_exe WaveEquation {
  root := `examples.WaveEquation
  moreLinkArgs := moreLinkArgs
}

lean_exe HelloWorld {
  root := `examples.HelloWorld
  moreLinkArgs := moreLinkArgs
}


lean_exe HarmonicOscillator {
  root := `examples.HarmonicOscillator
  moreLinkArgs := moreLinkArgs
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
  moreLinkArgs := moreLinkArgs
}

lean_exe LBFGS {
  root := `Test.optimjl.lbfgs
  moreLinkArgs := moreLinkArgs
}

lean_exe GMM {
  root := `SciLean.Examples.GMM.Main
  moreLinkArgs := moreLinkArgs
}

lean_exe BlasTest {
  root := `examples.BlasTest
  moreLinkArgs := moreLinkArgs
}

lean_exe FloatTest {
  root := `examples.FloatTest
  moreLinkArgs := moreLinkArgs
}

lean_exe ForLoopTest {
  buildType := .release
  moreLinkArgs := #["-O3", "-UNDEBUG"]
  root := `tests.sum_speed_test
}

lean_exe SurfaceMeshTests {
  root := `examples.SurfaceMeshTests
  moreLinkArgs := moreLinkArgs
}

lean_exe FloatMatrixTest {
  root := `examples.FloatMatrixTest
  moreLinkArgs := moreLinkArgs
}

lean_exe MNISTClassifier where
  root := `examples.MNISTClassifier



meta if get_config? doc = some "dev" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "master"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"
require leanblas from git "https://github.com/lecopivo/LeanBLAS" @ "master"

set_option linter.unusedVariables false

/--

  Compiles all lean files 'test/*.lean

    lake script run tests

 -/
script tests (args) do
  let cwd ← IO.currentDir
  -- let testDir := cwd / "test"
  let searchPath := SearchPath.toString
                      ["build" / "lib",
                       "lean_packages" / "mathlib" / "build" / "lib"]

  let mut testNum : Nat := 0
  let mut failedTests : Array (FilePath × IO.Process.Output) := #[]

  for test in (← (cwd / "test").readDir) do
    if test.path.extension == some "lean" then
      testNum := testNum + (1 : Nat)

      let r ← timeit s!"Running test: {test.fileName}\t" (IO.Process.output {
        cmd := "lean"
        args := #[test.path.toString]
        env := #[("LEAN_PATH", searchPath)]
      })

      if r.exitCode == (0 : UInt32) then
        IO.println "  Success!"
      else
        failedTests := failedTests.append #[(test.path, r)]
        IO.println "  Failed!"

  if failedTests.size != 0 then
    IO.println "\nFailed tests:"
    for (test, _) in failedTests do
      IO.println s!"  {test}"

  IO.println s!"\nSuccessful tests: {testNum - failedTests.size} / {testNum}"

  return 0
