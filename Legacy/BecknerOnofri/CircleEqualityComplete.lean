module

public import Legacy.BecknerOnofri.CircleEqualityClassification
public import Legacy.BecknerOnofri.FiniteEnergyGreenIdentification

@[expose] public section

/-! The complete circle equality statements, including arbitrary means,
finite-entropy densities and the manuscript's singular Green integral. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
open TorusSobolev SubcriticalAttainment SubcriticalEuler SobolevCentering
set_option maxHeartbeats 1200000

theorem center_eq_potential_iff {u : TorusL2 1} (hr : RealPotential u)
    {z : ℂ} (hz : ‖z‖ < 1) :
    center u = potential z hz ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure 1] fun x => ((logPotential z x+c : ℝ) : ℂ) := by
  constructor
  · intro he
    refine ⟨∫ x, (u x).re ∂torusMeasure 1, ?_⟩
    have ha := potential_ae hz
    rw [← he] at ha
    filter_upwards [center_real_ae u, ha, hr] with x hc hp hi
    apply Complex.ext
    · have h := congrArg Complex.re hp
      simp only [Complex.ofReal_re] at h ⊢
      linarith
    · simpa only [Complex.ofReal_im] using hi
  · rintro ⟨c, he⟩
    have hm : (∫ x, (u x).re ∂torusMeasure 1) = c := by
      rw [← translated_mean hz c]
      apply integral_congr_ae
      filter_upwards [he] with x hx
      simp only [hx, Complex.ofReal_re]
    apply Lp.ext
    filter_upwards [center_real_ae u, center_real hr, potential_ae hz, he]
      with x hc hi hp hu
    rw [hp]
    apply Complex.ext
    · simp only [hu, Complex.ofReal_re, hm] at hc
      simpa only [Complex.ofReal_re, add_sub_cancel_right] using hc
    · simpa only [Complex.ofReal_im] using hi

theorem onofri_equality_iff_logarithmic_family {u : TorusL2 1}
    (hr : RealPotential u) (hs : Summable (weightedSquare (fourierIsometry 1 u))) :
    Real.log (EndpointPotential.centeredPartition u) =
      (1/(4*(1:ℝ)*endpointSymbolConstant 1))*EndpointPotential.manuscriptEnergy u ↔
      ∃ z : ℂ, ‖z‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => ((logPotential z x+c : ℝ) : ℂ) := by
  have hcoef := EndpointPotential.coefficient_manuscript (by decide : 0<1) u hs
  simp only [Nat.cast_one, mul_one] at hcoef ⊢
  rw [← hcoef, EndpointPotential.centeredPartition_eq, ← center_energy (by decide : 0<1) u,
    potential_equality_iff (center_admissible (by decide : 0<1) hr hs)]
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, (center_eq_potential_iff hr hz).mp he⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, (center_eq_potential_iff hr hz).mpr he⟩

theorem onofri_equality_iff_paper_family {u : TorusL2 1}
    (hr : RealPotential u) (hs : Summable (weightedSquare (fourierIsometry 1 u))) :
    Real.log (EndpointPotential.centeredPartition u) =
      (1/(4*(1:ℝ)*endpointSymbolConstant 1))*EndpointPotential.manuscriptEnergy u ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x =>
          ((-2*Real.log ‖1-conj a*fourier 1 (x 0)‖+c : ℝ) : ℂ) := by
  rw [onofri_equality_iff_logarithmic_family hr hs]
  constructor
  · rintro ⟨z, hz, c, he⟩
    refine ⟨conj z, by simpa only [Complex.norm_conj] using hz, c, ?_⟩
    simpa only [logPotential, character_eq_fourier, starRingEnd_self_apply] using he
  · rintro ⟨a, ha, c, he⟩
    refine ⟨conj a, by simpa only [Complex.norm_conj] using ha, c, ?_⟩
    simpa only [logPotential_paper] using he

theorem density_equality_iff_poisson (r : ProbabilityDensity 1) (hr : r.FiniteEntropy) :
    endpointConstant 1*fourierEnergy r = densityEntropy r.value ↔
      ∃ z : ℂ, ‖z‖ < 1 ∧ r.value =ᵐ[torusMeasure 1] poisson z := by
  constructor
  · intro he
    obtain ⟨u, hu, heq, hg⟩ := EndpointEqualityCorrespondence.exists_potential_equality
      (by decide : 0<1) endpoint_one r hr he
    obtain ⟨z, hz, huEq⟩ := potential_of_equality hu heq
    rw [huEq] at hg
    exact ⟨z, hz, hg.trans (poisson_gibbs hz)⟩
  · rintro ⟨z, hz, he⟩
    have hf (k : Frequency 1) : densityFourier r.value k = densityFourier (poisson z) k := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    have henergy : fourierEnergy r = fourierEnergy (poissonDensity z hz) := by
      apply tsum_congr
      intro k
      simp only [densitySpectralTerm, hf]
      rfl
    rw [henergy, EndpointMaximizerLevel.densityEntropy_congr_ae he]
    exact poisson_equality hz

theorem density_equality_iff_paper_family (r : ProbabilityDensity 1) (hr : r.FiniteEntropy) :
    endpointConstant 1*fourierEnergy r = densityEntropy r.value ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ r.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2 := by
  rw [density_equality_iff_poisson r hr]
  constructor
  · rintro ⟨z, hz, he⟩
    refine ⟨conj z, by simpa only [Complex.norm_conj] using hz, ?_⟩
    simpa only [← poisson_paper, starRingEnd_self_apply] using he
  · rintro ⟨a, ha, he⟩
    refine ⟨conj a, by simpa only [Complex.norm_conj] using ha, ?_⟩
    filter_upwards [he] with x hx
    simpa only [poisson_paper] using hx

theorem physical_green_equality_iff_paper_family (r : ProbabilityDensity 1)
    (hr : r.FiniteEntropy) :
    PhysicalGreenL2.physicalGreenEnergy r = densityEntropy r.value ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ r.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2 := by
  rw [FiniteEnergyGreenIdentification.finiteEntropy_physicalGreen_eq_spectral
    (by decide : 1≤1) (by decide : 1≤10) r hr]
  have he : densitySpectralEnergy r = endpointConstant 1*fourierEnergy r := by
    rw [normalized_energy]
    unfold endpointConstant
    norm_num
    ring
  rw [he]
  exact density_equality_iff_paper_family r hr

#print axioms onofri_equality_iff_paper_family
#print axioms density_equality_iff_paper_family
#print axioms physical_green_equality_iff_paper_family
end Legacy.BecknerOnofri.CircleEquality
