import Lake
open Lake DSL System

package scilean 

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"f16c2788554b9960de815ae1e3f25de8c722bde4"

@[defaultTarget]
lean_lib SciLean {
  roots := #[`SciLean]
}

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

-- Builds all literate *.lean files in doc/literate and saves them to
-- build/doc/literate
script literate (args) do
  let cwd ← IO.currentDir

  for file in (← (cwd / "doc" / "literate").readDir) do
    if file.path.extension == some "lean" then
      
      IO.println s!"Building literate lean file: {file.path.toString}"

      let _ ← IO.Process.output {
        cmd := "alectryon"
        args := #["--lake", "lakefile.lean", "--output-directory", "build/doc/literate", file.path.toString]
      }

  return 0

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
