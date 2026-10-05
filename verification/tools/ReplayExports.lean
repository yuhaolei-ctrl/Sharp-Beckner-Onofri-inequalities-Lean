module

/- Replay exact on-disk exports with the pinned Comparator libraries.
This driver changes only input transport (file streams instead of String buffers)
and progress reporting. It does not alter matching or kernel algorithms. -/
public import Comparator
public import Lean4Checker.Replay
public import Export.Parse

@[expose] public section

open Lean

structure ReplayConfig where
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  deriving FromJson

def report (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def readExport (path : System.FilePath) : IO Export.ExportedEnv :=
  IO.FS.withFile path .read fun h => Export.parseStream (IO.FS.Stream.ofHandle h)

-- Same primitive roots as Comparator.Main at the pinned revision.
def primitiveRoots : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList]

def main (args : List String) : IO Unit := do
  let [configPath, challengePath, solutionPath] := args
    | throw (.userError "Usage: replay-exports CONFIG CHALLENGE.ndjson SOLUTION.ndjson")
  let config : ReplayConfig ← IO.ofExcept <| fromJson? <| ← IO.ofExcept <|
    Json.parse (← IO.FS.readFile configPath)
  let theorems := config.theorem_names.map String.toName
  let definitions := config.definition_names.getD #[] |>.map String.toName
  let axioms := config.permitted_axioms.map String.toName
  report s!"Parsing challenge export for {theorems.size} registered targets."
  let challenge ← readExport challengePath
  report s!"Challenge parsed: {challenge.constMap.size} declarations."
  let solution ← readExport solutionPath
  report s!"Solution parsed: {solution.constMap.size} declarations."
  IO.ofExcept <| Comparator.compareAt challenge solution (theorems ++ axioms)
    definitions primitiveRoots
  report "Comparator accepts all registered statements and reachable definitions."
  IO.ofExcept <| Comparator.checkAxioms solution theorems definitions axioms
  report "Comparator accepts axiom dependencies."
  report "Running Lean default kernel on solution."
  let env ← Lean.mkEmptyEnvironment
  -- The official kernel adds these alongside Quot, as in Comparator.Main.
  let constants := solution.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay' constants
  report "Lean default kernel accepts the solution"
  report "Your solution is okay!"
