import Legacy.BecknerOnofri.CircleEqualityDensity

/-! Exact parameter and normalization identification with the manuscript's circle family. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
open TorusSobolev SubcriticalAttainment

theorem character_eq_fourier (x : Torus 1) : character x = fourier 1 (x 0) := by
  simp [character, UnitAddTorus.mFourier, frequency]

theorem denominator_paper (a : ℂ) (x : Torus 1) :
    ‖1 - conj a * character x‖ = ‖character x - a‖ := by
  have hunit : character x * conj (character x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, character_norm]
    norm_num
  have he : 1 - conj a * character x = character x * conj (character x - a) := by
    rw [map_sub, mul_sub, hunit]
    ring
  rw [he, norm_mul, character_norm, Complex.norm_conj, one_mul]

theorem poisson_paper (a : ℂ) (x : Torus 1) :
    poisson (conj a) x = (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2 := by
  rw [poisson, Complex.norm_conj, denominator_paper, character_eq_fourier]

theorem logPotential_paper (a : ℂ) (x : Torus 1) :
    logPotential (conj a) x = -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ := by
  rw [logPotential, character_eq_fourier]

theorem paper_family_attains (a : ℂ) (ha : ‖a‖ < 1) :
    ∃ u : TorusL2 1, Admissible u ∧
      u =ᵐ[torusMeasure 1] (fun x => ((-2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ : ℝ) : ℂ)) ∧
      Real.log (partition u) = EndpointPotential.coefficient 1 * criticalEnergy u := by
  have hz : ‖conj a‖ < 1 := by simpa only [Complex.norm_conj] using ha
  refine ⟨potential (conj a) hz, potential_admissible hz, ?_, potential_equality hz⟩
  simpa only [logPotential_paper] using potential_ae hz

theorem potential_fourier_nat {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    fourierIsometry 1 (potential z hz) (frequency (n : ℤ)) = z ^ n / (n : ℂ) := by
  rw [potential_fourier hz]
  rfl

theorem poisson_fourier_nat {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    densityFourier (poisson z) (frequency (n : ℤ)) = z ^ n := by
  rw [poisson_fourier hz]
  rfl

theorem translated_mean {z : ℂ} (hz : ‖z‖ < 1) (c : ℝ) :
    (∫ x, logPotential z x + c ∂torusMeasure 1) = c := by
  rw [integral_add ((logPotential_continuous hz).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (integrable_const c),
    logPotential_mean hz, integral_const, probReal_univ, one_smul, zero_add]

theorem translated_centered {z : ℂ} (hz : ‖z‖ < 1) (c : ℝ) (x : Torus 1) :
    logPotential z x + c - (∫ y, logPotential z y + c ∂torusMeasure 1) = logPotential z x := by
  rw [translated_mean hz c]
  ring

#print axioms paper_family_attains
#print axioms poisson_paper
end Legacy.BecknerOnofri.CircleEquality
