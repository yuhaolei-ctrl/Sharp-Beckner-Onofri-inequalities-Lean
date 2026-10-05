import Legacy.BecknerOnofri.CircleEqualityEnergy

/-! The actual Poisson family attains the circle entropy endpoint. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
open TorusSobolev SubcriticalAttainment SubcriticalEuler
set_option maxHeartbeats 800000

theorem poisson_equality {z : ℂ} (hz : ‖z‖ < 1) :
    endpointConstant 1 * fourierEnergy (poissonDensity z hz) = densityEntropy (poisson z) := by
  let u := potential z hz
  let hR := EndpointPotential.rough_of_endpoint (by norm_num : 0 < 1) endpoint_one
  let r := gibbsDensity hR (potential_admissible hz)
  have h := EndpointPotential.gibbs_equality_of_potential_equality (by norm_num : 0 < 1)
    endpoint_one (potential_admissible hz) (potential_equality hz)
  have hf (k : Frequency 1) : densityFourier r.value k = densityFourier (poisson z) k := by
    unfold densityFourier
    apply integral_congr_ae
    filter_upwards [poisson_gibbs hz] with x hx
    change _ * (gibbsValue (potential z hz) x : ℂ) = _
    rw [hx]
  have hspec : densitySpectralTerm r = densitySpectralTerm (poissonDensity z hz) := by
    funext k
    simp only [densitySpectralTerm, hf]
    rfl
  have hent : densityEntropy (gibbsValue (potential z hz)) = densityEntropy (poisson z) := by
    apply integral_congr_ae
    filter_upwards [poisson_gibbs hz] with x hx
    rw [hx]
  change endpointConstant 1 * (∑' k, densitySpectralTerm r k) = _ at h
  rw [hspec, hent] at h
  exact h

theorem geometric_weighted (z : ℂ) (k : Frequency 1) :
    ‖coefficient (geometricCoefficient z) k‖ ^ 2 / frequencyRadius k ^ 1 =
      energySeries z (k 0).natAbs := by
  rw [frequencyRadius_one, pow_one]
  unfold coefficient
  cases h : k 0 with
  | ofNat n =>
    change ‖z ^ n‖ ^ 2 / |(n : ℝ)| = energySeries z n
    rw [norm_pow, abs_of_nonneg (Nat.cast_nonneg n), energySeries, pow_right_comm]
  | negSucc n =>
    simp only [integerCoefficient, geometricCoefficient, Complex.norm_conj, norm_pow,
      Int.natAbs_negSucc, Int.cast_negSucc, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    unfold energySeries
    rw [pow_right_comm]

theorem poisson_energy {z : ℂ} (hz : ‖z‖ < 1) :
    fourierEnergy (poissonDensity z hz) = -2 * Real.log (1 - ‖z‖ ^ 2) := by
  have hterm (k : NonzeroFrequency 1) : densitySpectralTerm (poissonDensity z hz) k =
      energySeries z (k.val 0).natAbs := by
    unfold densitySpectralTerm
    change ‖densityFourier (poisson z) k.val‖ ^ 2 / _ = _
    rw [poisson_fourier hz, geometric_weighted]
  unfold fourierEnergy
  simp_rw [hterm]
  have hsupport : Function.support (fun k : Frequency 1 => energySeries z (k 0).natAbs) ⊆
      {k | k ≠ 0} := by
    intro k hk hz0
    subst k
    exact hk (by simp [energySeries])
  convert! (tsum_subtype_eq_of_support_subset hsupport).trans (energy_hasSum hz).tsum_eq using 1

theorem poisson_entropy {z : ℂ} (hz : ‖z‖ < 1) :
    densityEntropy (poisson z) = -Real.log (1 - ‖z‖ ^ 2) := by
  rw [← poisson_equality hz, endpointConstant_one, poisson_energy hz]
  ring

/-- Explicit pointwise Gibbs normalization of the paper's logarithmic potential. -/
theorem poisson_normalized_exponential {z : ℂ} (hz : ‖z‖ < 1) (x : Torus 1) :
    Real.exp (logPotential z x) / (∫ y, Real.exp (logPotential z y) ∂torusMeasure 1) = poisson z x := by
  rw [logPotential_partition hz, exp_logPotential hz]
  have hd : 1 - ‖z‖ ^ 2 ≠ 0 := (sub_pos.mpr (normSq_parameter_lt_one hz)).ne'
  field_simp

#print axioms poisson_equality
#print axioms poisson_energy
#print axioms poisson_entropy
end Legacy.BecknerOnofri.CircleEquality
