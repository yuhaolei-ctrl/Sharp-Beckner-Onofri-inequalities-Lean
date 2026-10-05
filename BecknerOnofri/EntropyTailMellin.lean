import BecknerOnofri.EntropyTailIntegralDefinitions
import BecknerOnofri.EntropyTailHeat
import Legacy.BecknerOnofri.GaussianMellinTerm
import Legacy.TorusEndpoint.IntegrableSeries

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.GaussianLattice

/-- Normalized individual Mellin summands. -/
def mellinTerm (η : ℝ) (k : Frequency 12) (s : ℝ) : ℝ :=
  (s-η)^5 * heatTerm s k / 120

theorem outsideCube_square_pos {k : Frequency 12} (hk : outsideCube k) :
    0 < (latticeSquare k : ℝ) := by
  have hn : k ≠ 0 := by
    intro hz
    subst k
    obtain ⟨i,hi⟩ := hk
    simp at hi
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((latticeSquare_eq_zero_iff k).not.mpr hn))

theorem mellinTerm_integrable (η : ℝ) (k : Frequency 12) :
    IntegrableOn (mellinTerm η k) (Ioi η) := by
  change Integrable (fun s : ℝ => (s-η)^5 * heatTerm s k / 120) (volume.restrict (Ioi η))
  by_cases hk : outsideCube k
  · have h := Legacy.BecknerOnofri.GaussianMellinTerm.shifted_integrable
      (s := 6) (by norm_num) (outsideCube_square_pos hk) η
    norm_num only [show (6 : ℝ)-1=5 by norm_num, Real.rpow_ofNat] at h
    convert! h.div_const 120 using 1
    simp only [heatTerm, if_pos hk, gaussian,
      Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq, latticeSquare_cast]
  · simp only [mellinTerm, heatTerm, if_neg hk, mul_zero, zero_div]
    exact integrable_zero _ _ _

theorem mellinTerm_integral (η : ℝ) (k : Frequency 12) :
    (∫ s in Ioi η, mellinTerm η k s) =
      scalarTailWeight k * Real.exp (-η * ∑ i : Fin 12, (k i : ℝ)^2) := by
  by_cases hk : outsideCube k
  · have h := Legacy.BecknerOnofri.GaussianMellinTerm.shifted_integral
      (s := 6) (by norm_num) (outsideCube_square_pos hk) η
    have hG : Real.Gamma 6 = 120 := by
      have h := Real.Gamma_nat_eq_factorial 5
      norm_num at h ⊢
    norm_num only [show (6 : ℝ)-1=5 by norm_num, Real.rpow_ofNat, hG] at h
    have hp : frequencyLength k^12 = (latticeSquare k : ℝ)^6 := by
      have hh := frequencyLength_pow_eq k
      norm_num only [Nat.cast_ofNat, show (12 : ℝ)/2 = 6 by norm_num, Real.rpow_ofNat] at hh
      exact hh
    simp only [mellinTerm, heatTerm, scalarTailWeight, if_pos hk, gaussian,
      Legacy.TorusEndpoint.GreenMultiplierSummability.radiusSq, hp]
    rw [integral_div, ← latticeSquare_cast, h]
    ring
  · simp [mellinTerm, heatTerm, scalarTailWeight, hk]

theorem mellinTerm_nonneg {η s : ℝ} (hs : η ≤ s) (k : Frequency 12) :
    0 ≤ mellinTerm η k s := by
  exact div_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr hs) _) (heatTerm_nonneg s k)) (by norm_num)

theorem mellinTerm_norm_integral (η : ℝ) (k : Frequency 12) :
    (∫ s in Ioi η, ‖mellinTerm η k s‖) =
      scalarTailWeight k * Real.exp (-η * ∑ i : Fin 12, (k i : ℝ)^2) := by
  rw [← mellinTerm_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact Real.norm_of_nonneg (mellinTerm_nonneg hs.le k)

theorem mellinTerm_sum {η s : ℝ} (hs : 0 < s) :
    (∑' k : Frequency 12, mellinTerm η k s) = (s-η)^5 * heatComplement s / 120 := by
  simp only [mellinTerm, div_eq_mul_inv, tsum_mul_right, tsum_mul_left,
    ← heatComplement_eq_tsum hs]

theorem normalized_heat_integrable {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun s : ℝ => (s-η)^5 * heatComplement s / 120) (Ioi η) := by
  have hs : Summable (fun k : Frequency 12 => ∫ s in Ioi η, ‖mellinTerm η k s‖) := by
    simp_rw [mellinTerm_norm_integral]
    exact gaussianTail_summable hη
  apply (Legacy.TorusEndpoint.IntegrableSeries.integrable_tsum_of_summable_integral_norm
    (mellinTerm_integrable η) hs).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mellinTerm_sum (hη.trans hs)

theorem heatIntegral_eq_gaussianTail {η : ℝ} (hη : 0 < η) :
    heatIntegral η = gaussianTail η := by
  have hs : Summable (fun k : Frequency 12 => ∫ s in Ioi η, ‖mellinTerm η k s‖) := by
    simp_rw [mellinTerm_norm_integral]
    exact gaussianTail_summable hη
  have h := integral_tsum_of_summable_integral_norm (mellinTerm_integrable η) hs
  simp only [mellinTerm_integral] at h
  change gaussianTail η = _ at h
  rw [h]
  unfold heatIntegral
  rw [show (1/120 : ℝ) * (∫ s in Ioi η, (s-η)^5 * heatComplement s) =
      ∫ s in Ioi η, (s-η)^5 * heatComplement s / 120 by rw [integral_div]; ring]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (mellinTerm_sum (hη.trans hs)).symm

theorem scalarTail_le_heatIntegral {n : ℕ} (hn : 0 < n) :
    scalarTail n ≤ heatIntegral (1/((n : ℝ)+1/2)) := by
  rw [heatIntegral_eq_gaussianTail (by positivity)]
  exact scalarTail_le_gaussianTail hn

#print axioms heatIntegral_eq_gaussianTail
#print axioms scalarTail_le_heatIntegral
end BecknerOnofri.HighDim.EntropyTail
