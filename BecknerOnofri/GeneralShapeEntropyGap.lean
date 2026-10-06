module

public import BecknerOnofri.GeneralShapeFourierEntropy
public import BecknerOnofri.SelectedEntropyRigidity
public import BecknerOnofri.EntropyCertifiedWitness
public import BecknerOnofri.EntropyTailCertifiedScalar

@[expose] public section

/-! The full nonstationary entropy comparison from the shape assumptions,
using the already checked scalar and spin certificates. -/
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

/-- The channel entropy pays for the actual singular Fourier tail. The scalar
numerical estimate remains explicit until its separate certificate is complete. -/
theorem entropy_minus_tail
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    {ρ : ProbabilityDensity 12} (D : Data ρ)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    2*Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw ρ)) Spin.reference+
      12*ψ (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) ≤
        HighDim.entropy ρ-(1/2 : ℝ)*(∑' k : Frequency 12,
          EntropyTail.scalarTailWeight k*‖HighDim.fourierCoeff ρ.value k‖^2) := by
  have htail := tail_of_scalar hscalar D
  have hent := (channel_fourier_entropy D ψ hc hcv hminor).2
  linarith


theorem entropy_deficit
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    {ρ : ProbabilityDensity 12} (D : Data ρ)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    Spin.functional (Spin.countLaw (Spin.channelLaw ρ))+
      12*ψ (Spin.mean (Spin.countLaw (Spin.channelLaw ρ))) ≤
        HighDim.entropy ρ-(1/2 : ℝ)*EntropyTail.fullFourierEnergy ρ.value := by
  have htail := entropy_minus_tail hscalar D ψ hc hcv hminor
  have hcube := Spin.cube_half_energy_eq_quadratic ρ (Data.mixture D)
    (exchangeable D)
  have hsplit := EntropyTail.fullFourierEnergy_split (continuous_density D)
  unfold Spin.functional
  linarith


theorem gap_of_certificates
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))
    {ρ : ProbabilityDensity 12} (D : Data ρ) :
    (Spin.mean (Spin.countLaw (Spin.channelLaw ρ)))^4/250 ≤
      HighDim.entropy ρ-(1/2 : ℝ)*EntropyTail.fullFourierEnergy ρ.value :=
  (hspin _ (feasible D) (spin_mean_range D)).trans
    (entropy_deficit hscalar D ψ hc hcv hminor)


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


/-- Complete numerical and analytic closure for a general shape density. -/
theorem global_gap {ρ : ProbabilityDensity 12} (D : Data ρ) :
    (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re^4/250≤
      entropy ρ-(1/2 : ℝ)*EntropyTail.fullFourierEnergy ρ.value := by
  obtain ⟨ψ,hc,hcv,_,_,_,hm,hs⟩ := exists_certified_entropy_minorant
  have h := gap_of_certificates EntropyTail.scalarTail_le_budget ψ hc hcv hm hs D
  rw [density_axis_re D,density_axis_mean D]
  exact h

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
