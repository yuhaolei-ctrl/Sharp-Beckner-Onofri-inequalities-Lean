module

public import BecknerOnofri.GeneralShapeFourierEntropy
public import BecknerOnofri.SelectedEntropyRigidity
public import BecknerOnofri.GeneralShapeEntropyEta
public import BecknerOnofri.SpinFiniteStateInequality
public import BecknerOnofri.EntropyTailLarge
public import BecknerOnofri.TwelveNumericalInputs

@[expose] public section

/-! Proposition 5.10 (prop:section5-global-entropy-gap) for every density satisfying the shape
hypotheses: Proposition 5.11 (via Lemma 5.13), Proposition 5.12(i) with the Jensen remainder,
and Proposition 5.12(ii) (via Lemmas 5.17 and 5.20). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ShapeEntropy
open Legacy.TorusEndpoint Legacy.BecknerOnofri TorusSobolev

theorem tail_of_scalar
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    {ρ : ProbabilityDensity 12} (D : Data ρ) :
    (1/2 : ℝ)*(∑' k : Frequency 12,
      EntropyTail.scalarTailWeight k*‖HighDim.fourierCoeff ρ.value k‖^2) ≤
      (21/1000)*(∑ i : Fin 12, ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2)+
        (67/100)*(∑ i : Fin 12, ∑' j : ℕ,
          ‖HighDim.fourierCoeff ρ.value (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  obtain ⟨w,N,hw,hm,hSup,he⟩ := Data.mixture D
  rw [he]
  have h := EntropyTail.countable_mixture_tail_of_scalar hscalar w N hw hm.summable hSup
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact h

theorem uniform_of_mean_zero {ρ : ProbabilityDensity 12} (D : Data ρ)
    (hz : Spin.mean (Spin.countLaw (Spin.channelLaw ρ))=0) :
    ρ.value=(fun _ => 1) := by
  apply EntropyMixtureRigidity.positive_mixture_uniform (Data.mixture D)
  intro i
  have he : axisFrequency i = (Pi.single i (1 : ℤ) : Frequency 12) := by
    ext j
    simp [axisFrequency, Pi.single_apply]
  rw [he]
  have hn := density_axis_norm_sq D i 1
  rw [density_axis_mean D, hz] at hn
  have hn0 : ‖HighDim.fourierCoeff ρ.value (Pi.single i (1 : ℤ))‖=0 := by
    nlinarith [norm_nonneg (HighDim.fourierCoeff ρ.value (Pi.single i (1 : ℤ)))]
  exact norm_eq_zero.mp hn0


/-- **Proposition 5.10** for a general admissible density:
`Ent(ρ) - ½ ∑_{k≠0} |k|^{-12} |ρ̂(k)|² ≥ ρ̂(e₁)⁴/200`. -/
theorem global_gap {ρ : ProbabilityDensity 12} (D : Data ρ) :
    (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re ^ 4 / 200 ≤
      entropy ρ - (1/2 : ℝ) * EntropyTail.fullFourierEnergy ρ.value := by
  have htail := tail_of_scalar EntropyTail.scalarTail_le_budget D
  have hent := (channel_fourier_entropy_eta D psi_le_gamma).2
  have hcube := Spin.cube_half_energy_eq_quadratic ρ (Data.mixture D) (exchangeable D)
  have hsplit := EntropyTail.fullFourierEnergy_split (continuous_density D)
  have hspin := Spin.finite_state_inequality_of_pressure pressureScalar_gt (spin_mean_range D)
    (p := Spin.countLaw (Spin.channelLaw ρ)) ⟨feasible D, rfl⟩
  unfold Spin.penalized Spin.functional at hspin
  rw [density_axis_re D, density_axis_mean D]
  linarith

lemma first_mode_nonnegative {ρ : ProbabilityDensity 12} (D : Data ρ) :
    0≤(fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re := by
  rw [density_axis_re D,density_axis_mean D]
  exact (spin_mean_range D).1

lemma first_mode_zero_uniform {ρ : ProbabilityDensity 12} (D : Data ρ)
    (hz : (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re=0) :
    ρ.value=(fun _ => 1) := by
  rw [density_axis_re D,density_axis_mean D] at hz
  exact uniform_of_mean_zero D hz

#print axioms global_gap
#print axioms first_mode_nonnegative
#print axioms first_mode_zero_uniform
end BecknerOnofri.HighDim.ShapeEntropy
