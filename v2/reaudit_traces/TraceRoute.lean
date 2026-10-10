import SolutionRoute
import BecknerOnofri.V2.Reaudit.Final.All
import BecknerOnofri.V2.Reaudit.ExternalInputs.CriticalAdams
import BecknerOnofri.AdamsEndpointPressure
import BecknerOnofri.HeatGreenPairing
open Lean Meta Elab Command

/-- Modules of the old low-dimension endpoint chain and the old statement/consequence layers. -/
def forbidden : List String := ["Legacy.BecknerOnofri.PaperResults", "Legacy.BecknerOnofri.Targets",
  "Legacy.BecknerOnofri.OnsetConsequences", "Legacy.BecknerOnofri.PressureSecondDerivative",
  "Legacy.BecknerOnofri.PressureDerivativeOnset", "Legacy.BecknerOnofri.PressureCurvatureOnset",
  "Legacy.BecknerOnofri.low_density_rigidity", "Legacy.BecknerOnofri.LowDimensionMixtureEndpoint",
  "Legacy.BecknerOnofri.EndpointThroughTen", "BecknerOnofri.PaperResults", "BecknerOnofri.Targets",
  "BecknerOnofri.OnsetConsequences", "BecknerOnofri.PressureSecondDerivative",
  "BecknerOnofri.PressureDerivativeOnset", "BecknerOnofri.PressureCurvatureOnset",
  "BecknerOnofri.low_density_rigidity", "BecknerOnofri.LowDimensionMixtureEndpoint",
  "BecknerOnofri.EndpointThroughTen"]

def modName (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "<current>"

def usedOf (env : Environment) (n : Name) : Array Name := Id.run do
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

def pathTo (parent : Std.HashMap Name Name) (n : Name) : String := Id.run do
  let mut p := [n]
  let mut cur := n
  for _ in [0:200] do
    match parent[cur]? with
    | some q => p := q :: p; cur := q
    | none => break
  return " -> ".intercalate (p.map toString)

def idxSet (env : Environment) (pred : String → Bool) : Std.HashSet Nat := Id.run do
  let mut r : Std.HashSet Nat := {}
  for h : i in [0:env.header.moduleNames.size] do
    if pred (env.header.moduleNames[i]).toString then r := r.insert i
  return r

def usedCached (env : Environment) (cache : IO.Ref (Std.HashMap Name (Array Name))) (n : Name) :
    IO (Array Name) := do
  if let some r := (← cache.get)[n]? then return r
  let r := usedOf env n
  cache.modify (·.insert n r)
  return r

def traceOne (env : Environment) (cache : IO.Ref (Std.HashMap Name (Array Name)))
    (forb sec3 leg : Std.HashSet Nat) (t : Name) : IO String := do
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {}
  let mut q : Array Name := #[t]
  seen := seen.insert t
  let mut i := 0
  let mut axs : Array Name := #[]
  let mut hits : Array (Name × String) := #[]
  let mut nsec3 := 0
  let mut nleg := 0
  let mut sorryUsed := false
  while i < q.size do
    let n := q[i]!
    i := i + 1
    match env.find? n with
    | some (.axiomInfo _) => axs := axs.push n
    | _ => pure ()
    if n == ``sorryAx then sorryUsed := true
    if let some mi := env.getModuleIdxFor? n then
      let k := mi.toNat
      if forb.contains k then hits := hits.push (n, (env.header.moduleNames[k]!).toString)
      if sec3.contains k then nsec3 := nsec3 + 1
      if leg.contains k then nleg := nleg + 1
    for c in (← usedCached env cache n) do
      unless seen.contains c do
        seen := seen.insert c
        parent := parent.insert c n
        q := q.push c
  let ex := hits.toList.take 3 |>.map fun (n, m) => s!"{n}@{m} via {pathTo parent n}"
  return s!"{t}\t{q.size}\t{axs.toList}\t{sorryUsed}\t{hits.size}\t{nsec3}\t{nleg}\t{ex}\n"

/-- Groups of targets, each written to its own file; one shared cache of per-constant dependencies. -/
elab "#trace_groups " gs:term : command => do
  let env ← getEnv
  let forb := idxSet env fun m => forbidden.any (fun p => m.startsWith p)
  let sec3 := idxSet env fun m => m.startsWith "BecknerOnofri.V2.Section3"
  let leg := idxSet env fun m => m.startsWith "Legacy."
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let groups ← liftTermElabM do
    let e ← Term.elabTerm gs (some (← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``String, ← mkAppM ``List #[mkConst ``Name]]]))
    Term.synthesizeSyntheticMVarsNoPostponing
    unsafe evalExpr (List (String × List Name)) (← inferType e) e
  for (out, ids) in groups do
    let mut text := "target\tn_constants\taxioms\tsorryAx\tforbidden_hits\tSection3_consts\tLegacy_consts\texamples\n"
    for n in ids do
      text := text ++ (← traceOne env cache forb sec3 leg n)
    IO.FS.writeFile out text
    logInfo m!"wrote {out}"

#trace_groups [
 ("/tmp/trace_lowdim.tsv", [
  ``BecknerOnofri.low_dim_entropy_inequality, ``BecknerOnofri.low_dim_beckner_onofri,
  ``BecknerOnofri.low_dim_coefficient_sharp, ``BecknerOnofri.circle_beckner_onofri_eq_iff,
  ``BecknerOnofri.circle_entropy_eq_iff, ``BecknerOnofri.low_dim_entropy_eq_iff,
  ``BecknerOnofri.low_dim_beckner_onofri_eq_iff, ``BecknerOnofri.low_dim_pressure_eq,
  ``BecknerOnofri.low_dim_defect_eq, ``BecknerOnofri.low_dim_globalTransition]),
 ("/tmp/trace_eleven.tsv", [
  ``BecknerOnofri.V2.Reaudit.ElevenBounds.mixture_gap_eleven,
  ``BecknerOnofri.V2.Reaudit.ElevenBounds.beta0_le_globalTransition_quantitative,
  ``BecknerOnofri.V2.Reaudit.ElevenBounds.uniform_unique_quantitative,
  ``BecknerOnofri.V2.Reaudit.Compactness.coexistence,
  ``BecknerOnofri.V2.Reaudit.Compactness.strict_lower_of_coexistence_manuscript,
  ``BecknerOnofri.V2.Reaudit.Final.strict_lower_route,
  ``BecknerOnofri.V2.Reaudit.Final.prop49_route,
  ``BecknerOnofri.V2.Reaudit.Final.prop41_route,
  ``BecknerOnofri.V2.Reaudit.Final.theorem_1_2_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_globalTransition_bounds_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_coexistence_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_competitor_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_spectral_pressure_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_uniform_hessian_pos_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_pressure_corner_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_pressure_derivative_jump_route,
  ``BecknerOnofri.V2.Reaudit.Final.eleven_defect_corner_route,
  ``BecknerOnofri.eleven_profile_constant, ``BecknerOnofri.eleven_competitor,
  ``BecknerOnofri.eleven_globalTransition_bounds, ``BecknerOnofri.eleven_coexistence,
  ``BecknerOnofri.eleven_uniform_hessian_pos, ``BecknerOnofri.eleven_pressure_corner,
  ``BecknerOnofri.eleven_pressure_derivative_jump, ``BecknerOnofri.eleven_defect_corner]),
 ("/tmp/trace_highdim.tsv", [
  ``BecknerOnofri.high_dim_entropy_inequality, ``BecknerOnofri.high_dim_entropy_eq_iff,
  ``BecknerOnofri.high_dim_beckner_onofri, ``BecknerOnofri.high_dim_beckner_onofri_eq_iff,
  ``BecknerOnofri.high_dim_thresholds, ``BecknerOnofri.kappa_pos,
  ``BecknerOnofri.high_dim_onset_branch, ``BecknerOnofri.high_dim_pressure_onset,
  ``BecknerOnofri.high_dim_defect_onset, ``BecknerOnofri.V2.Final.Unconditional.high_endpoint]),
 ("/tmp/trace_modular.tsv", [
  ``BecknerOnofri.V2.ThetaTail.RouteM.twelve_square_routeM,
  ``BecknerOnofri.V2.ThetaTail.RouteM.Tn_le_Rn]),
 ("/tmp/trace_external.tsv", [
  ``BecknerOnofri.V2.Reaudit.ExternalInputs.positiveThreshold,
  ``BecknerOnofri.V2.Reaudit.ExternalInputs.criticalAdams,
  ``BecknerOnofri.V2.Reaudit.ExternalInputs.circleLebedevMilin,
  ``BecknerOnofri.HighDim.critical_adams_bound,
  ``BecknerOnofri.AdamsEndpoint.circle_heatInteraction_entropy,
  ``BecknerOnofri.V2.Reaudit.ExternalInputs.critical_adams_bound_indep,
  ``BecknerOnofri.V2.Reaudit.ExternalInputs.circle_heatInteraction_entropy_indep])]
