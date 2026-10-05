import BecknerOnofri.EntropyHeatDerivative

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.GaussianLattice

def slopeMellinTerm (η : ℝ) (k : Frequency 12) (s : ℝ) : ℝ :=
  (s-η)^4 * heatTerm s k / 24

theorem slopeMellinTerm_integrable (η : ℝ) (k : Frequency 12) :
    IntegrableOn (slopeMellinTerm η k) (Ioi η) := by
  change Integrable (fun s : ℝ => (s-η)^4 * heatTerm s k / 24) (volume.restrict (Ioi η))
  by_cases hk : outsideCube k
  · have h := Legacy.BecknerOnofri.GaussianMellinTerm.shifted_integrable
      (s := 5) (by norm_num) (outsideCube_square_pos hk) η
    norm_num only [show (5 : ℝ)-1=4 by norm_num, Real.rpow_ofNat] at h
    convert! h.div_const 24 using 1
    simp only [heatTerm, if_pos hk, gaussian,
      Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq, latticeSquare_cast]
  · simp only [slopeMellinTerm, heatTerm, if_neg hk, mul_zero, zero_div]
    exact integrable_zero _ _ _

theorem slopeMellinTerm_integral (η : ℝ) (k : Frequency 12) :
    (∫ s in Ioi η, slopeMellinTerm η k s) =
      scalarTailWeight k * frequencySquare k * Real.exp (-η * frequencySquare k) := by
  by_cases hk : outsideCube k
  · have h := Legacy.BecknerOnofri.GaussianMellinTerm.shifted_integral
      (s := 5) (by norm_num) (outsideCube_square_pos hk) η
    have hG : Real.Gamma 5 = 24 := by
      have h := Real.Gamma_nat_eq_factorial 4
      norm_num at h ⊢
    norm_num only [show (5 : ℝ)-1=4 by norm_num, Real.rpow_ofNat, hG] at h
    have hp : frequencyLength k^12 = (latticeSquare k : ℝ)^6 := by
      have hh := frequencyLength_pow_eq k
      norm_num only [Nat.cast_ofNat, show (12 : ℝ)/2 = 6 by norm_num, Real.rpow_ofNat] at hh
      exact hh
    have hR : (latticeSquare k : ℝ) ≠ 0 := (outsideCube_square_pos hk).ne'
    simp only [slopeMellinTerm, heatTerm, scalarTailWeight, if_pos hk, gaussian,
      Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq, hp, frequencySquare]
    rw [integral_div, ← latticeSquare_cast, h]
    field_simp
    <;> ring
  · simp [slopeMellinTerm, heatTerm, scalarTailWeight, hk]

theorem slopeMellinTerm_nonneg (η s : ℝ) (k : Frequency 12) :
    0 ≤ slopeMellinTerm η k s :=
  div_nonneg (mul_nonneg (by positivity) (heatTerm_nonneg s k)) (by norm_num)

theorem slopeMellinTerm_norm_integral (η : ℝ) (k : Frequency 12) :
    (∫ s in Ioi η, ‖slopeMellinTerm η k s‖) =
      scalarTailWeight k * frequencySquare k * Real.exp (-η * frequencySquare k) := by
  simp only [Real.norm_of_nonneg (slopeMellinTerm_nonneg η _ k), slopeMellinTerm_integral]

theorem slopeMellinTerm_sum {η s : ℝ} (hs : 0 < s) :
    (∑' k : Frequency 12, slopeMellinTerm η k s) = (s-η)^4 * heatComplement s / 24 := by
  simp only [slopeMellinTerm, div_eq_mul_inv, tsum_mul_right, tsum_mul_left,
    ← heatComplement_eq_tsum hs]

theorem slope_heat_integrable {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun s : ℝ => (s-η)^4 * heatComplement s) (Ioi η) := by
  have hs : Summable (fun k : Frequency 12 => ∫ s in Ioi η, ‖slopeMellinTerm η k s‖) := by
    simp_rw [slopeMellinTerm_norm_integral]
    exact gaussianSlope_summable hη
  have hi := Legacy.TorusEndpoint.IntegrableSeries.integrable_tsum_of_summable_integral_norm
    (slopeMellinTerm_integrable η) hs
  have hn : IntegrableOn (fun s : ℝ => (s-η)^4 * heatComplement s / 24) (Ioi η) := by
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact slopeMellinTerm_sum (hη.trans hs)
  change Integrable (fun s : ℝ => (s-η)^4 * heatComplement s) (volume.restrict (Ioi η))
  simpa only [div_mul_cancel₀ _ (by norm_num : (24 : ℝ) ≠ 0)] using hn.mul_const 24

theorem gaussianSlope_eq_heatIntegral {η : ℝ} (hη : 0 < η) :
    gaussianSlope η = (1/24 : ℝ)*(∫ s in Ioi η, (s-η)^4 * heatComplement s) := by
  have hs : Summable (fun k : Frequency 12 => ∫ s in Ioi η, ‖slopeMellinTerm η k s‖) := by
    simp_rw [slopeMellinTerm_norm_integral]
    exact gaussianSlope_summable hη
  have h := integral_tsum_of_summable_integral_norm (slopeMellinTerm_integrable η) hs
  simp only [slopeMellinTerm_integral] at h
  change gaussianSlope η = _ at h
  rw [h, show (1/24 : ℝ) * (∫ s in Ioi η, (s-η)^4 * heatComplement s) =
      ∫ s in Ioi η, (s-η)^4 * heatComplement s / 24 by rw [integral_div]; ring]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact slopeMellinTerm_sum (hη.trans hs)

#print axioms gaussianSlope_eq_heatIntegral
end BecknerOnofri.HighDim.EntropyTail
