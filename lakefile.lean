import Lake
open Lake DSL System

package scilean

@[default_target]
lean_lib SciLean {
  -- precompileModules := true
  roots := #[`SciLean]
}


lean_exe WaveEquation {
  root := `examples.WaveEquation
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

lean_exe ForLoopTest {
  buildType := .release
  moreLinkArgs := #["-O3", "-UNDEBUG"]
  root := `tests.sum_speed_test
}

lean_exe SurfaceMeshTests {
  root := `examples.SurfaceMeshTests
}

lean_exe MNISTClassifier where
  root := `examples.MNISTClassifier



meta if get_config? doc = some "dev" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "master"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

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


script compileEigen (args) do

  -- make build directory
  let makeBuildDir ← IO.Process.run {
    cmd := "mkdir"
    args := #["-p", "build/Eigen"]
  }

  -- run cmake
  if ¬(← defaultBuildDir / "Eigen" / "Makefile" |>.pathExists) then
    let runCMake ← IO.Process.spawn {
      cmd := "cmake"
      args := #[(← IO.currentDir) / "cpp" / "Eigen" |>.toString, 
                "-DCMAKE_EXPORT_COMPILE_COMMANDS=1",
                "-DCMAKE_BUILD_TYPE=Release",
                s!"-DCMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES={← getLeanIncludeDir}"]
      cwd := defaultBuildDir / "Eigen" |>.toString
      
    }
    let out ← runCMake.wait
    if out != 0 then
      return out

  -- run make 
  let runMake ← IO.Process.spawn {
    cmd := "make"
    args := #["-j"]
    cwd := defaultBuildDir / "Eigen" |>.toString
  }
  let out ← runMake.wait
  if out != 0 then
    return out 

  return 0


/--

  Compiles literate lean file 'doc/literate/harmonic_oscillator.lean'
and places the result to 'build/doc/literate'

    lake script run literate doc/literate/harmonic_oscillator.lean

  Compiles all literate lean files 'doc/literate/*.lean' and places
the result to 'build/doc/literate'

    lake scipt run literate
 -/
script literate (args) do
  let cwd ← IO.currentDir

  -- Copy css files
  let copyCss : IO Unit := do
    let alectryonSrc := cwd / "doc" / "literate" / "alectryon.css"
    let alectryonTrg := cwd / "build" / "doc" / "literate" / "alectryon.css"
    let pygmentsSrc := cwd / "doc" / "literate" / "pygments.css"
    let pygmentsTrg := cwd / "build" / "doc" / "literate" / "pygments.css"

    let _ ← IO.Process.output {
      cmd := "cp"
      args := #[alectryonSrc.toString, alectryonTrg.toString]
    }
    let _ ← IO.Process.output {
      cmd := "cp"
      args := #[pygmentsSrc.toString, pygmentsTrg.toString]
    }


  -- Build files specified on the input
  if ¬ args.isEmpty then
    for f in args do
      let file := cwd / f

      IO.println s!"Building literate lean file: {file}"

      let _ ← IO.Process.output {
        cmd := "alectryon"
        args := #["--no-header", "--lake", "lakefile.lean", "--output-directory", "build/doc/literate", file.toString]
      }

    copyCss

    return 0

  -- Build all literate files
  for file in (← (cwd / "doc" / "literate").readDir) do
    if file.path.extension == some "lean" then

      IO.println s!"Building literate lean file: {file.path.toString}"

      let _ ← IO.Process.output {
        cmd := "alectryon"
        args := #["--no-header", "--lake", "lakefile.lean", "--output-directory", "build/doc/literate", file.path.toString]
      }

  copyCss

  return 0
