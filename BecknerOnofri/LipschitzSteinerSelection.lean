module

public import BecknerOnofri.PolarizationOrbitClosure
public import BecknerOnofri.PolarizationUniformL1
public import BecknerOnofri.BoundedMomentFunctional
public import Legacy.BecknerOnofri.SteinerSelection

@[expose] public section

/-! Compact orbit selection for arbitrary Lipschitz functions, independent of
variational optimality or Euler equations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri CoordinatePolarization

theorem exists_fixed_orbit_limit {d : ℕ} (f : Torus d → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ g : Torus d →ᵇ ℝ,g∈closure (boundedOrbit f) ∧ LipschitzWith K g ∧
      IdentDistrib g f (torusMeasure d) (torusMeasure d) ∧ OriginPolarizationInvariant g := by
  let fB : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f,hf.continuous⟩
  let w : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨CosineMomentWeight.weight d,CosineMomentWeight.weight_continuous d⟩
  have hcompact := compact_orbit_closure f hf (fun x => fB.norm_coe_le_norm x)
  have hnonempty : (closure (boundedOrbit f)).Nonempty :=
    ⟨fB,subset_closure (show fB∈boundedOrbit f from Orbit.refl)⟩
  obtain ⟨g,hg,hmax⟩ := hcompact.exists_isMaxOn hnonempty (boundedMoment_continuous w).continuousOn
  refine ⟨g,hg,closure_lipschitz hf hg,?_,?_⟩
  · obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hg
    exact bounded_orbit_limit_identDistrib (fB.integrable _) hu htu
  · intro i a ha ha0
    have hg2 : MemLp g 2 (torusMeasure d) :=
      g.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hw2 := CosineMomentWeight.weight_memLp d
    have hs := CosineMomentWeight.weight_strict i ha ha0
    have hm : ∀ x∈halfTorus i a,CosineMomentWeight.weight d (reflection i a x)≤CosineMomentWeight.weight d x := by
      intro x hx
      by_cases he : reflection i a x=x
      · rw [he]
      · exact (hs x hx he).le
    have hlower := moment_polarize_le i a hg2 hw2 hm
    have hupper := hmax (closure_polarize hf hg i a)
    change (∫ x,polarize i a g x*CosineMomentWeight.weight d x ∂torusMeasure d)≤
      ∫ x,g x*CosineMomentWeight.weight d x ∂torusMeasure d at hupper
    exact polarize_ae_eq_of_moment_eq i a hg2 hw2 hs (le_antisymm hlower hupper)

/-- A genuine equimeasurable, coordinatewise symmetric decreasing orbit limit
exists for every Lipschitz function. In one dimension this is the usual
symmetric decreasing rearrangement existence step. -/
theorem exists_steiner_orbit_limit {d : ℕ} (f : Torus d → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ g : Torus d →ᵇ ℝ,g∈closure (boundedOrbit f) ∧ LipschitzWith K g ∧
      IdentDistrib g f (torusMeasure d) (torusMeasure d) ∧ SteinerSelection.Steiner g := by
  obtain ⟨g,hg,hL,hD,hfixed⟩ := exists_fixed_orbit_limit f hf
  exact ⟨g,hg,hL,hD,SteinerSelection.steiner_of_origin_invariant g.continuous hfixed⟩

#print axioms exists_fixed_orbit_limit
#print axioms exists_steiner_orbit_limit
end BecknerOnofri.PolarizationL1
