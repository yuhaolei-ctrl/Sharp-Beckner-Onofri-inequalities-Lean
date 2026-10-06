module

public import BecknerOnofri.CoordinatePolarizationFibers
public import BecknerOnofri.PolarizationOrbitClosure
public import BecknerOnofri.BoundedMomentFunctional
public import Legacy.BecknerOnofri.SteinerSelection

@[expose] public section

/-! Compact selection using only one coordinate. Full fiber distributions
are retained, permitting subsequent identification with canonical rearrangement. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri CoordinatePolarization

def boundedOrbit {d : ℕ} (i : Fin d) (f : Torus d → ℝ) : Set (Torus d →ᵇ ℝ) :=
  {g | Orbit i f g}

lemma closure_subset_full {d : ℕ} (i : Fin d) (f : Torus d → ℝ) :
    closure (boundedOrbit i f) ⊆ closure (PolarizationL1.boundedOrbit f) :=
  closure_mono (fun _ hg => hg.global)

lemma closure_lipschitz {d : ℕ} {i : Fin d} {f : Torus d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit i f)) :
    LipschitzWith K g := PolarizationL1.closure_lipschitz hf (closure_subset_full i f hg)

theorem compact_orbit_closure {d : ℕ} (i : Fin d) (f : Torus d → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) : IsCompact (closure (boundedOrbit i f)) := by
  let fB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f,hf.continuous⟩
  exact (PolarizationL1.compact_orbit_closure f hf (fun x => fB.norm_coe_le_norm x)).of_isClosed_subset
    isClosed_closure (closure_subset_full i f)

theorem closure_polarize {d : ℕ} {i : Fin d} {f : Torus d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit i f)) (a : ℝ) :
    PolarizationL1.boundedPolarize i a g (closure_lipschitz hf hg) ∈ closure (boundedOrbit i f) := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
  have huL (n : ℕ) : LipschitzWith K (u n) := (hu n).global.lipschitz hf
  let v : ℕ → Torus d →ᵇ ℝ := fun n => PolarizationL1.boundedPolarize i a (u n) (huL n)
  have hv (n : ℕ) : v n∈boundedOrbit i f := Orbit.step (hu n) a
  have htv : Tendsto v atTop (𝓝 (PolarizationL1.boundedPolarize i a g (closure_lipschitz hf hg))) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact PolarizationL1.polarize_tendstoUniformly i a
      (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu)
  exact mem_closure_of_tendsto htv (Eventually.of_forall hv)

theorem closure_fiber_identDistrib {d : ℕ} {i : Fin d} {f : Torus d → ℝ}
    (hf : Continuous f) {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit i f)) (x : Torus d) :
    IdentDistrib (fiber i g x) (fiber i f x) (torusMeasure 1) (torusMeasure 1) := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
  exact orbit_uniform_limit_fiber_identDistrib hf hu
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu) x

theorem exists_fixed_coordinate_limit {d : ℕ} (i : Fin d) (f : Torus d → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ g : Torus d →ᵇ ℝ, g∈closure (boundedOrbit i f) ∧ LipschitzWith K g ∧
      (∀ x, IdentDistrib (fiber i g x) (fiber i f x) (torusMeasure 1) (torusMeasure 1)) ∧
      ∀ a : ℝ, -(1/2:ℝ)<a → a<0 → polarize i a g=g := by
  let fB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f,hf.continuous⟩
  let w : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨CosineMomentWeight.weight d,CosineMomentWeight.weight_continuous d⟩
  obtain ⟨g,hg,hmax⟩ := (compact_orbit_closure i f hf).exists_isMaxOn
    ⟨fB,subset_closure (show fB∈boundedOrbit i f from Orbit.refl)⟩
    (PolarizationL1.boundedMoment_continuous w).continuousOn
  have hgL := closure_lipschitz hf hg
  refine ⟨g,hg,hgL,closure_fiber_identDistrib hf.continuous hg,?_⟩
  intro a ha ha0
  have hg2 : MemLp g 2 (torusMeasure d) :=
    g.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw2 := CosineMomentWeight.weight_memLp d
  have hs := CosineMomentWeight.weight_strict i ha ha0
  have hm : ∀ x∈halfTorus i a, CosineMomentWeight.weight d (reflection i a x)≤CosineMomentWeight.weight d x := by
    intro x hx
    by_cases he : reflection i a x=x
    · rw [he]
    · exact (hs x hx he).le
  have hupper := hmax (closure_polarize hf hg a)
  change (∫ x,polarize i a g x*CosineMomentWeight.weight d x ∂torusMeasure d) ≤
    ∫ x,g x*CosineMomentWeight.weight d x ∂torusMeasure d at hupper
  have he := polarize_ae_eq_of_moment_eq i a hg2 hw2 hs
    (le_antisymm (moment_polarize_le i a hg2 hw2 hm) hupper)
  haveI : (torusMeasure d).IsOpenPosMeasure := by rw [torusMeasure_explicit]; infer_instance
  exact Measure.eq_of_ae_eq he (PolarizationL1.polarize_lipschitz i a hgL).continuous g.continuous

#print axioms exists_fixed_coordinate_limit
end BecknerOnofri.CoordinateRearrangement
