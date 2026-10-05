import BecknerOnofri.EntropyTailMixedHeat
import BecknerOnofri.EntropyTailMellin

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail

def mixedMellinTerm (L : Fin 12 → ℕ) (k : Frequency 12) (s : ℝ) : ℝ :=
  mixedCoefficient L k * mellinTerm 0 k s

theorem mixedMellinTerm_integrable (L : Fin 12 → ℕ) (k : Frequency 12) :
    IntegrableOn (mixedMellinTerm L k) (Ioi 0) :=
  (mellinTerm_integrable 0 k).const_mul _

theorem mixedMellinTerm_integral (L : Fin 12 → ℕ) (k : Frequency 12) :
    (∫ s in Ioi 0, mixedMellinTerm L k s) = scalarTailWeight k*mixedCoefficient L k := by
  unfold mixedMellinTerm
  rw [integral_const_mul, mellinTerm_integral]
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, one_mul, mul_comm]

theorem mixedMellinTerm_norm_integral (L : Fin 12 → ℕ) (k : Frequency 12) :
    (∫ s in Ioi 0, ‖mixedMellinTerm L k s‖) = scalarTailWeight k*mixedCoefficient L k := by
  rw [← mixedMellinTerm_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact Real.norm_of_nonneg (mul_nonneg (mixedCoefficient_nonneg L k)
    (mellinTerm_nonneg hs.le k))

theorem mixedMellinTerm_sum (L : Fin 12 → ℕ) (s : ℝ) :
    (∑' k, mixedMellinTerm L k s) = s^5*mixedHeat s L/120 := by
  simp only [mixedMellinTerm, mellinTerm, sub_zero]
  simp_rw [show ∀ k, mixedCoefficient L k * (s^5 * heatTerm s k / 120) =
    s^5 / 120 * (mixedCoefficient L k * heatTerm s k) by intro k; ring]
  rw [tsum_mul_left]
  unfold mixedHeat
  ring

theorem normalized_mixedHeat_integrable (L : Fin 12 → ℕ) :
    IntegrableOn (fun s : ℝ => s^5*mixedHeat s L/120) (Ioi 0) := by
  have hs : Summable (fun k : Frequency 12 => ∫ s in Ioi 0, ‖mixedMellinTerm L k s‖) := by
    simp_rw [mixedMellinTerm_norm_integral]
    exact mixedTail_summable L
  have h :=
    Legacy.TorusEndpoint.IntegrableSeries.integrable_tsum_of_summable_integral_norm
      (mixedMellinTerm_integrable L) hs
  simp only [mixedMellinTerm_sum] at h
  change Integrable (fun s : ℝ => s^5*mixedHeat s L/120) (volume.restrict (Ioi 0))
  exact h

theorem mixedTail_eq_heatIntegral (L : Fin 12 → ℕ) :
    mixedTail L = ∫ s in Ioi 0, s^5*mixedHeat s L/120 := by
  have hs : Summable (fun k : Frequency 12 => ∫ s in Ioi 0, ‖mixedMellinTerm L k s‖) := by
    simp_rw [mixedMellinTerm_norm_integral]
    exact mixedTail_summable L
  have h := integral_tsum_of_summable_integral_norm (mixedMellinTerm_integrable L) hs
  simpa only [mixedMellinTerm_integral, mixedMellinTerm_sum, mixedTail] using h

theorem mixedTail_diagonal (n : ℕ) : mixedTail (fun _ => n) = scalarTail n := rfl

/-- The manuscript's unequal-index comparison, for the actual singular Fourier tail. -/
theorem mixedTail_le_diagonal (L : Fin 12 → ℕ) :
    mixedTail L ≤ (1/12 : ℝ)*∑ i : Fin 12, scalarTail (L i) := by
  simp_rw [← mixedTail_diagonal, mixedTail_eq_heatIntegral]
  rw [← integral_finsetSum _ (fun i _ => normalized_mixedHeat_integrable (fun _ => L i)),
    ← integral_const_mul]
  apply integral_mono_ae (normalized_mixedHeat_integrable L)
    ((integrable_finsetSum _ (fun i _ => normalized_mixedHeat_integrable (fun _ => L i))).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have h := mul_le_mul_of_nonneg_left (mixedHeat_le_diagonal hs0 L)
    (show 0 ≤ s^5/120 by positivity)
  convert! h using 1
  · ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

#print axioms mixedTail_le_diagonal
end BecknerOnofri.HighDim.EntropyTail
