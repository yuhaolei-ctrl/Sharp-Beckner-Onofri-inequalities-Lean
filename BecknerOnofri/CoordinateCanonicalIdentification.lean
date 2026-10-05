module

public import BecknerOnofri.CoordinateOrbitCompact
public import BecknerOnofri.CircleLayerCakeIdentification
public import BecknerOnofri.CircleRearrangementDefinitions

@[expose] public section

/-! Identification of the one-coordinate compact orbit limit with the
canonical layer-cake rearrangement, fiber by fiber. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.CoordinateRearrangement
open Legacy.BecknerOnofri CoordinatePolarization

lemma fiber_steiner_of_fixed {d : ℕ} (i : Fin d) {g : Torus d → ℝ}
    (hg : Continuous g)
    (hfixed : ∀ a : ℝ, -(1/2:ℝ)<a → a<0 → polarize i a g=g) (x : Torus d) :
    SteinerSelection.Steiner (fiber i g x) := by
  apply SteinerSelection.steiner_of_origin_invariant (fiber_continuous i hg x)
  intro j a ha ha0
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  rw [← fiber_polarize,hfixed a ha ha0]

/-- Each fiber is the literal circle layer-cake rearrangement almost
everywhere, with a globally Lipschitz representative and no optimality premise. -/
theorem exists_canonical_coordinate_limit {d : ℕ} (i : Fin d) (f : Torus d → ℝ) {K : ℝ≥0}
    (hf : LipschitzWith K f) (hf0 : ∀ x, 0≤f x) :
    ∃ g : Torus d →ᵇ ℝ, g∈closure (boundedOrbit i f) ∧ LipschitzWith K g ∧
      (∀ x, IdentDistrib (fiber i g x) (fiber i f x) (torusMeasure 1) (torusMeasure 1)) ∧
      (∀ x, SteinerSelection.Steiner (fiber i g x)) ∧
      ∀ x, Circle.realRearrange (fiber i f x) =ᵐ[torusMeasure 1] fiber i g x := by
  obtain ⟨g,hg,hgL,hD,hfixed⟩ := exists_fixed_coordinate_limit i f hf
  have hS (x : Torus d) := fiber_steiner_of_fixed i g.continuous hfixed x
  refine ⟨g,hg,hgL,hD,hS,?_⟩
  intro x
  have hRad : DistributionLimit.AntitoneRadiusAE (torusMeasure 1)
      (fun z : Torus 1 => ‖z 0‖) (fiber i g x) :=
    ⟨univ,Eventually.of_forall (fun _ => mem_univ _),fun z _ w _ hzw =>
      PolarizationL1.steiner_antitone_radius (hS x) z w hzw⟩
  have he := PolarizationL1.layerRearrangement_eq_ofReal_of_measurable
    (fiber_continuous i g.continuous x).measurable (hD x) hRad
  have hpos : ∀ᵐ z ∂torusMeasure 1,0≤fiber i g x z :=
    (hD x).symm.ae_snd measurableSet_Ici (Eventually.of_forall (fun z => hf0 _))
  filter_upwards [he,hpos] with z hz hz0
  change (PolarizationL1.layerRearrangement (fiber i f x) z).toReal = _
  rw [hz,ENNReal.toReal_ofReal hz0]

#print axioms exists_canonical_coordinate_limit
end BecknerOnofri.CoordinateRearrangement
