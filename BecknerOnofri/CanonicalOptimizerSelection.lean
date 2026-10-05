module

public import BecknerOnofri.SuccessiveCoordinateRearrangement
public import BecknerOnofri.UniformPolarizationMaximizers
public import BecknerOnofri.PolarizationUniformL1

@[expose] public section

/-! Finite canonical coordinate rearrangement of a prescribed optimizer,
with its full distribution and variational optimality preserved. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri GibbsL2Continuity SubcriticalDensityCompactness
open HighDim.CoordinateRearrangementStatement

lemma closure_identDistrib {d : ℕ} {i : Fin d} (f : Torus d →ᵇ ℝ)
    {g : Torus d →ᵇ ℝ} (hg : g∈closure (boundedOrbit i f)) :
    IdentDistrib g f (torusMeasure d) (torusMeasure d) := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp (closure_subset_full i f hg)
  exact PolarizationL1.bounded_orbit_limit_identDistrib (f.integrable _) hu htu

theorem canonical_optimizer_selection {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d)<A) (f : Torus d →ᵇ ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hf0 : ∀ x,0≤f x)
    (hmax : BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ f ∈ densityMaximizers d A) :
    ∃ g : Torus d →ᵇ ℝ, SuccessiveSteiner f g ∧ LipschitzWith K g ∧ (∀ x,0≤g x) ∧
      BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ g ∈ densityMaximizers d A ∧
      IdentDistrib g f (torusMeasure d) (torusMeasure d) ∧ SteinerSelection.Steiner g := by
  let P : (Torus d →ᵇ ℝ) → Prop := fun g =>
    BoundedContinuousFunction.toLp 2 (torusMeasure d) ℝ g ∈ densityMaximizers d A ∧
      IdentDistrib g f (torusMeasure d) (torusMeasure d)
  have hP (i : Fin d) (u v : Torus d →ᵇ ℝ) (_ : LipschitzWith K u)
      (hv : v∈closure (boundedOrbit i u)) (hu : P u) : P v := by
    have hu2 : MemLp u 2 (torusMeasure d) :=
      u.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine ⟨PrescribedPolarization.uniformClosure_mem_maximizers hd hA hu2 ?_
      (closure_subset_full i u hv),(closure_identDistrib u hv).trans hu.2⟩
    rw [← PrescribedPolarization.bounded_toLp_eq u hu2]
    exact hu.1
  obtain ⟨g,hchain,hg,hg0,hgP,hgS,_⟩ := exists_canonical_chain (List.finRange d) P hP
    f hf hf0 ⟨hmax,IdentDistrib.refl f.continuous.aemeasurable⟩
  refine ⟨g,hchain,hg,hg0,hgP.1,hgP.2,?_,?_⟩
  · intro i x
    exact (hgS i (List.mem_finRange i)).1 x
  · intro x i
    exact (hgS i (List.mem_finRange i)).2 x

#print axioms canonical_optimizer_selection
end BecknerOnofri.CoordinateRearrangement
