module

public import Legacy.BecknerOnofri.CircleEqualityFamily

@[expose] public section

/-! Actual critical Sobolev membership and equality for the conformal circle family. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
open TorusSobolev SubcriticalAttainment
set_option maxHeartbeats 800000

def potentialMap (z : ℂ) (hz : ‖z‖ < 1) : C(Torus 1, ℂ) :=
  ⟨fun x => (logPotential z x : ℂ), Complex.continuous_ofReal.comp (logPotential_continuous hz)⟩

def potential (z : ℂ) (hz : ‖z‖ < 1) : TorusL2 1 := (potentialMap z hz).toLp 2 (torusMeasure 1) ℂ

theorem potential_ae {z : ℂ} (hz : ‖z‖ < 1) :
    potential z hz =ᵐ[torusMeasure 1] (fun x => (logPotential z x : ℂ)) :=
  ContinuousMap.coeFn_toLp _ _

theorem potential_fourier {z : ℂ} (hz : ‖z‖ < 1) (k : Frequency 1) :
    fourierIsometry 1 (potential z hz) k = coefficient (logarithmicCoefficient z) k := by
  rw [fourierIsometry_apply]
  calc
    _ = UnitAddTorus.mFourierCoeff (fun x => (logPotential z x : ℂ)) k := by
      unfold UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      filter_upwards [potential_ae hz] with x hx
      rw [hx]
    _ = _ := logPotential_fourier hz k

def energySeries (z : ℂ) (n : ℕ) : ℝ := (‖z‖ ^ 2) ^ n / (n : ℝ)

theorem energySeries_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (energySeries z) (-Real.log (1 - ‖z‖ ^ 2)) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |‖z‖ ^ 2| < 1 by rw [abs_of_nonneg (sq_nonneg _)]; exact normSq_parameter_lt_one hz)
  have hshift : HasSum (fun n => energySeries z (n+1)) (-Real.log (1 - ‖z‖ ^ 2)) := by
    simpa only [energySeries, Nat.cast_add, Nat.cast_one] using h
  have hfull := (hasSum_nat_add_iff 1).mp hshift
  simpa [energySeries] using hfull

theorem weighted_logarithmic_nat (z : ℂ) (n : ℕ) :
    (n : ℝ) * ‖logarithmicCoefficient z n‖ ^ 2 = energySeries z n := by
  by_cases hn : n = 0
  · simp [hn, energySeries, logarithmicCoefficient]
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [logarithmicCoefficient, norm_div, norm_pow, Complex.norm_natCast, energySeries]
    field_simp
    rw [pow_right_comm]

theorem weighted_logarithmic (z : ℂ) (k : Frequency 1) :
    frequencyRadius k ^ 1 * ‖coefficient (logarithmicCoefficient z) k‖ ^ 2 =
      energySeries z (k 0).natAbs := by
  rw [frequencyRadius_one, pow_one]
  unfold coefficient
  cases h : k 0 with
  | ofNat n =>
    change |(n : ℝ)| * ‖logarithmicCoefficient z n‖ ^ 2 = energySeries z n
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    exact weighted_logarithmic_nat z n
  | negSucc n =>
    simp only [integerCoefficient, Complex.norm_conj, Int.natAbs_negSucc, Int.cast_negSucc, abs_neg]
    rw [abs_of_nonneg (by positivity)]
    simpa only [Nat.cast_add, Nat.cast_one] using weighted_logarithmic_nat z (n + 1)

theorem energy_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : Frequency 1 => energySeries z (k 0).natAbs)
      (-2 * Real.log (1 - ‖z‖ ^ 2)) := by
  have hs := energySeries_hasSum hz
  have hs1 : HasSum (fun n => energySeries z (n+1)) (-Real.log (1 - ‖z‖ ^ 2)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hs
    simpa [energySeries] using h
  have hi : HasSum (fun j : ℤ => energySeries z j.natAbs)
      (-Real.log (1 - ‖z‖ ^ 2) + -Real.log (1 - ‖z‖ ^ 2)) := by
    apply HasSum.of_nat_of_neg_add_one
    · simpa only [Int.natAbs_natCast] using hs
    · convert! hs1 using 1
  have h := CosineMixtureAxis.frequencyOneEquivInt.hasSum_iff.mpr hi
  convert! h using 1
  ring

theorem potential_energy {z : ℂ} (hz : ‖z‖ < 1) :
    criticalEnergy (potential z hz) = -2 * Real.log (1 - ‖z‖ ^ 2) := by
  unfold criticalEnergy coefficientEnergy weightedSquare
  simp_rw [potential_fourier hz, weighted_logarithmic]
  exact (energy_hasSum hz).tsum_eq

theorem potential_admissible {z : ℂ} (hz : ‖z‖ < 1) : Admissible (potential z hz) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [potential_ae hz] with x hx
    simp [hx]
  · rw [potential_fourier hz]
    simp [coefficient, integerCoefficient, logarithmicCoefficient]
  · have hs := (energy_hasSum hz).summable
    exact hs.congr (fun k => by
      simp only [weightedSquare, potential_fourier hz, weighted_logarithmic])

theorem potential_partition {z : ℂ} (hz : ‖z‖ < 1) :
    partition (potential z hz) = (1 - ‖z‖ ^ 2)⁻¹ := by
  rw [partition]
  have h : (∫ x, Real.exp ((potential z hz) x).re ∂torusMeasure 1) =
      ∫ x, Real.exp (logPotential z x) ∂torusMeasure 1 := by
    apply integral_congr_ae
    filter_upwards [potential_ae hz] with x hx
    simp only [hx, Complex.ofReal_re]
  rw [h, logPotential_partition hz]

theorem potential_equality {z : ℂ} (hz : ‖z‖ < 1) :
    Real.log (partition (potential z hz)) =
      EndpointPotential.coefficient 1 * criticalEnergy (potential z hz) := by
  rw [potential_partition hz, potential_energy hz, Real.log_inv,
    EndpointPotential.coefficient, endpointConstant_one]
  ring

theorem poisson_gibbs {z : ℂ} (hz : ‖z‖ < 1) :
    SubcriticalEuler.gibbsValue (potential z hz) =ᵐ[torusMeasure 1] poisson z := by
  filter_upwards [potential_ae hz] with x hx
  rw [SubcriticalEuler.gibbsValue, hx, Complex.ofReal_re, potential_partition hz,
    exp_logPotential hz]
  have hd : 1 - ‖z‖ ^ 2 ≠ 0 := (sub_pos.mpr (normSq_parameter_lt_one hz)).ne'
  field_simp

#print axioms potential_admissible
#print axioms potential_energy
#print axioms potential_equality
#print axioms poisson_gibbs
end Legacy.BecknerOnofri.CircleEquality
