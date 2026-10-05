module

public import BecknerOnofri.SelectedEntropyGap
public import BecknerOnofri.EntropyEnergySpectral
public import BecknerOnofri.EntropyMixtureRigidity
public import BecknerOnofri.Uniform

@[expose] public section

/-! Final analytic rigidity step of the entropy route. The scalar-tail and
finite-spin certificates remain explicit hypotheses until separately checked. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier

theorem selected_entropy_deficit_nonpos {u : TorusL2 12} (hu : Selected u) :
    HighDim.entropy (spinDensity hu) -
      (1/2 : ℝ)*EntropyTail.fullFourierEnergy (spinDensity hu).value ≤ 0 := by
  have he : EntropyTail.fullFourierEnergy (spinDensity hu).value =
      fourierEnergy (gibbsDensity rough hu.1) := by
    rw [EntropyTail.fullFourierEnergy_eq_spectral_tsum]
    unfold fourierEnergy
    apply tsum_congr
    intro k
    change (frequencyLength k.val^12)⁻¹ *
      ‖densityFourier (smoothGibbsDensity rough hu.1 (fourier_norm_summable hu)).value k.val‖^2 = _
    rw [smoothGibbsDensity_fourier]
    simp only [densitySpectralTerm, Bridge.frequencyLength_eq, div_eq_mul_inv, mul_comm]
    rfl
  have hent : HighDim.entropy (spinDensity hu) = densityEntropy (gibbsValue u) :=
    smoothGibbsDensity_entropy rough hu.1 (fourier_norm_summable hu)
  have hmax : 0 ≤ functional (1/2) u := by
    simpa using hu.2.1 0 (admissible_zero 12)
  rw [maximizer_functional_eq_density (by norm_num) rough
    (by norm_num : (0 : ℝ)<1/2) hu.1 hu.2.1] at hmax
  rw [he,hent]
  norm_num at hmax
  linarith

theorem selected_uniform_of_mean_zero {u : TorusL2 12} (hu : Selected u)
    (hz : Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))=0) :
    (spinDensity hu).value=(fun _ => 1) := by
  apply EntropyMixtureRigidity.positive_mixture_uniform (spinDensity_mixture hu)
  intro i
  have he : axisFrequency i = (Pi.single i (1 : ℤ) : Frequency 12) := by
    ext j
    simp [axisFrequency, Pi.single_apply]
  rw [he]
  have hn := density_axis_norm_sq hu i 1
  rw [density_axis_mean hu, hz] at hn
  have hn0 : ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (1 : ℤ))‖=0 := by
    nlinarith [norm_nonneg (HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (1 : ℤ)))]
  exact norm_eq_zero.mp hn0

theorem selected_zero_of_uniform {u : TorusL2 12} (hu : Selected u)
    (hρ : (spinDensity hu).value=(fun _ => 1)) : u=0 := by
  apply (fourierIsometry 12).injective
  ext k
  by_cases hk : k=0
  · subst k
    simp [hu.1.2.1]
  · have hmode : densityFourier (gibbsValue u) k=0 := by
      rw [← smoothGibbsDensity_fourier rough hu.1 (fourier_norm_summable hu)]
      change HighDim.fourierCoeff (spinDensity hu).value k=0
      rw [hρ]
      exact fourierCoeff_one_nonzero k hk
    rw [maximizer_fourier_formula rough (by norm_num : (0 : ℝ)<1/2) hu.1 hu.2.1 hk,
      hmode]
    simp

theorem selected_zero_of_entropy_certificates
    (hscalar : ∀ n : ℕ, EntropyTail.scalarTail n ≤ EntropyTail.scalarBudget n)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (hspin : ∀ q : Spin.Count → ℝ, Spin.Feasible q → Spin.mean q ∈ Icc (0 : ℝ) 1 →
      (Spin.mean q)^4/250 ≤ Spin.functional q+12*ψ (Spin.mean q))
    {u : TorusL2 12} (hu : Selected u) : u=0 := by
  have h := (selected_global_gap_of_certificates hscalar ψ hc hcv hminor hspin hu).trans
    (selected_entropy_deficit_nonpos hu)
  have hz : Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))=0 := by
    have h4 : (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))))^4=0 := by
      nlinarith [pow_nonneg (selected_spin_mean_range hu).1 4]
    exact (pow_eq_zero_iff (by decide : 4≠0)).mp h4
  exact selected_zero_of_uniform hu (selected_uniform_of_mean_zero hu hz)

#print axioms selected_zero_of_entropy_certificates
end BecknerOnofri.HighDim.SelectedNumericalModel
