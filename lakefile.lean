import Lake
open Lake DSL System

package SciLean {
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "e5b2b217243c699b8f3df18df98dcbb3ff57ab7c"
  }]
}

script tests (args) do
  let cwd ← IO.currentDir
  let testDir := cwd / "test"
  let searchPath := SearchPath.toString 
                      ["build" / "lib",
                       "lean_packages" / "mathlib" / "build" / "lib"]

  let mut testNum := 0
  let mut failedTests : Array (FilePath × IO.Process.Output) := #[]

  for test in (← (cwd / "test").readDir) do
    if test.path.extension == some "lean" then
      testNum := testNum + 1

      let r ← timeit s!"Running test: {test.fileName}\t" (IO.Process.output {
        cmd := "lean"
        args := #[test.path.toString]
        env := #[("LEAN_PATH", searchPath)]
      })
    
      if r.exitCode == 0 then
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
