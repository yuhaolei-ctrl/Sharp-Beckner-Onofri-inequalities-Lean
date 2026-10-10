import SolutionRoute
import SolutionV2
import BecknerOnofri.V2.Reaudit.Final.All
import BecknerOnofri.V2.Reaudit.ExternalInputs.CriticalAdams
open Lean Meta Elab Command

def usedOf2 (env : Environment) (n : Name) : Array Name := Id.run do
  match env.find? n with
  | none => return #[]
  | some ci =>
    let mut cs : Array Name := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    match ci with
    | .inductInfo i => cs := cs ++ i.ctors.toArray
    | .ctorInfo c => cs := cs ++ #[c.induct]
    | .recInfo r => cs := cs ++ #[r.getMajorInduct]
    | _ => pure ()
    return cs

def depClosure (env : Environment) (roots : Array Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut q := roots
  for r in roots do seen := seen.insert r
  let mut i := 0
  while i < q.size do
    let n := q[i]!
    i := i + 1
    for c in usedOf2 env n do
      unless seen.contains c do
        seen := seen.insert c
        q := q.push c
  return seen

/-- For every module: number of declarations and number reached from each root set. -/
elab "#reach " out:str : command => do
  let env ← getEnv
  let readRoots (f : String) : IO (Array Name) := do
    let s ← IO.FS.readFile f
    return (s.splitOn "\n").filter (· ≠ "") |>.map String.toName |>.toArray
  let r1 ← readRoots "/tmp/roots_route.txt"
  let r2 ← readRoots "/tmp/roots_v2.txt"
  let c1 := depClosure env r1
  let c2 := depClosure env r2
  let r3 := r1.filter fun n => (n.toString.splitOn "eleven").length > 1
  let c3 := depClosure env r3
  let mut tbl : Std.HashMap String (Nat × Nat × Nat × Nat) := {}
  for (c, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? c | continue
    let m := (env.header.moduleNames[mi.toNat]!).toString
    match ci with
    | .thmInfo _ | .defnInfo _ =>
      if c.isInternal then continue
      let (a, b, d, e) := tbl.getD m (0, 0, 0, 0)
      tbl := tbl.insert m (a + 1, b + (if c1.contains c then 1 else 0), d + (if c2.contains c then 1 else 0), e + (if c3.contains c then 1 else 0))
    | _ => pure ()
  let mut text := s!"module\tn_decls\treached_from_SolutionRoute({r1.size} roots)\treached_from_SolutionV2({r2.size} roots)\treached_from_eleven_roots({r3.size} roots)\n"
  for (m, (a, b, d, e)) in tbl.toList.toArray.qsort (fun x y => x.1 < y.1) do
    text := text ++ s!"{m}\t{a}\t{b}\t{d}\t{e}\n"
  IO.FS.writeFile out.getString text

#reach "/tmp/reach_by_module.tsv"
