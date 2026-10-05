import BecknerOnofri.LocalQsigma
import BecknerOnofri.LocalTiltedEstimates
import BecknerOnofri.LegacyBridge
import Legacy.BecknerOnofri.SobolevDensityPairing

/-! Actual Parseval and quadratic pairing bounds for higher Fourier modes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment

def HasOnlyHigherModes (u : TorusL2 12) : Prop :=
  ∀ k : Frequency 12, localRadiusSq k ≤ 1 → fourierIsometry 12 u k = 0

lemma higher_weight_pos (k : HigherFrequency 12) : 0 < frequencyLength k.val ^ 12 := by
  apply pow_pos
  unfold frequencyLength
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) (higher_radiusSq_ge_two k))

lemma higher_energy_hasSum (u : TorusL2 12) (hu : CriticalSobolev u) (hh : HasOnlyHigherModes u) :
    HasSum (fun k : HigherFrequency 12 => weightedSquare (fourierIsometry 12 u) k.val)
      (criticalEnergy u) := by
  have hsupp : Function.support (weightedSquare (fourierIsometry 12 u)) ⊆
      {k : Frequency 12 | 1 < localRadiusSq k} := by
    intro k hk
    by_contra h
    have hc := hh k (le_of_not_gt h)
    simp [weightedSquare, hc] at hk
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr hu.2.hasSum

lemma higher_norm_hasSum (u : TorusL2 12) (hh : HasOnlyHigherModes u) :
    HasSum (fun k : HigherFrequency 12 => ‖fourierIsometry 12 u k.val‖ ^ 2) (‖u‖ ^ 2) := by
  have hsupp : Function.support (fun k : Frequency 12 => ‖fourierIsometry 12 u k‖ ^ 2) ⊆
      {k : Frequency 12 | 1 < localRadiusSq k} := by
    intro k hk
    by_contra h
    have hc := hh k (le_of_not_gt h)
    simp [hc] at hk
  apply (hasSum_subtype_iff_of_support_subset hsupp).mpr
  have hs := summable_sq (fourierIsometry 12 u)
  have he := norm_sq_eq_tsum (fourierIsometry 12 u)
  rw [(fourierIsometry 12).norm_map] at he
  rw [he]
  exact hs.hasSum

lemma higher_norm_sq_le_energy (u : TorusL2 12) (hu : CriticalSobolev u) (hh : HasOnlyHigherModes u) :
    ‖u‖ ^ 2 ≤ (1 / 64 : ℝ) * criticalEnergy u := by
  have hs1 := higher_norm_hasSum u hh
  have hs2 := (higher_energy_hasSum u hu hh).mul_left (1 / 64 : ℝ)
  have h := hs1.summable.tsum_le_tsum (fun k => ?_) hs2.summable
  · rw [hs1.tsum_eq, hs2.tsum_eq] at h
    exact h
  · have hw : 1 ≤ (1 / 64 : ℝ) * frequencyLength k.val ^ 12 :=
      (div_le_iff₀ (higher_weight_pos k)).mp (by
        simpa only [one_div] using higher_inverse_twelfth_le k)
    have hp := mul_le_mul_of_nonneg_right hw (sq_nonneg ‖fourierIsometry 12 u k.val‖)
    simpa only [one_mul, weightedSquare, ← Bridge.frequencyLength_eq, mul_assoc] using hp

lemma higher_real_sq_integral_le_energy (u : TorusL2 12) (hu : CriticalSobolev u)
    (hh : HasOnlyHigherModes u) :
    (∫ x, (u x).re ^ 2 ∂torusMeasure 12) ≤ (1 / 64 : ℝ) * criticalEnergy u := by
  calc
    _ ≤ ∫ x, ‖u x‖ ^ 2 ∂torusMeasure 12 := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
        ((memLp_two_iff_integrable_sq_norm (Lp.memLp u).1).mp (Lp.memLp u))
      exact Filter.Eventually.of_forall (fun x => by
        change (u x).re ^ 2 ≤ ‖u x‖ ^ 2
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply]
        nlinarith [sq_nonneg (u x).im])
    _ = ‖u‖ ^ 2 := Legacy.BecknerOnofri.ExponentialPartitionContinuity.integral_norm_sq_Lp u
    _ ≤ _ := higher_norm_sq_le_energy u hu hh

lemma firstShellTilt_memLp {d : ℕ} (t : Fin d → ℝ) :
    MemLp (firstShellTilt t) 2 (torusMeasure d) := by
  apply Continuous.memLp_of_hasCompactSupport
  · unfold firstShellTilt circleTiltDensity circleCosine
    fun_prop
  · exact HasCompactSupport.of_compactSpace _

lemma higher_pairing_hasSum (u : TorusL2 12) (hh : HasOnlyHigherModes u) (t : Fin 12 → ℝ) :
    HasSum (fun k : HigherFrequency 12 =>
      (conj (fourierIsometry 12 u k.val) * fourierCoeff (firstShellTilt t) k.val).re)
      (∫ x, firstShellTilt t x * (u x).re ∂torusMeasure 12) := by
  have h := Legacy.BecknerOnofri.SobolevDensityPairing.hasSum_pairing u
    (Bridge.density (firstShellDensity t)) (firstShellTilt_memLp t)
  change HasSum (fun k : Frequency 12 =>
    (conj (fourierIsometry 12 u k) * fourierCoeff (firstShellTilt t) k).re)
    (∫ x, firstShellTilt t x * (u x).re ∂torusMeasure 12) at h
  have hsupp : Function.support (fun k : Frequency 12 =>
      (conj (fourierIsometry 12 u k) * fourierCoeff (firstShellTilt t) k).re) ⊆
      {k : Frequency 12 | 1 < localRadiusSq k} := by
    intro k hk
    by_contra hlow
    have hc := hh k (le_of_not_gt hlow)
    simp [hc] at hk
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr h

lemma higher_pairing_quadratic_bound (u : TorusL2 12) (hu : CriticalSobolev u)
    (hh : HasOnlyHigherModes u) (t : Fin 12 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (D : ℝ) (hD : 0 < D) :
    (∫ x, firstShellTilt t x * (u x).re ∂torusMeasure 12) ≤
      D / 2 * criticalEnergy u + localQsigma t / (2 * D) := by
  have hl := higher_pairing_hasSum u hh t
  have hr := ((higher_energy_hasSum u hu hh).mul_left (D / 2)).add
    ((localQsigma_summable t ht).hasSum.mul_left (1 / (2 * D)))
  have hpoint (k : HigherFrequency 12) :
      (conj (fourierIsometry 12 u k.val) * fourierCoeff (firstShellTilt t) k.val).re ≤
      D / 2 * weightedSquare (fourierIsometry 12 u) k.val +
        (1 / (2 * D)) * localQsigmaTerm t k := by
    have h := Legacy.BecknerOnofri.SobolevDensityPairing.quadratic_complex
      (b := 1 / (2 * D)) (w := frequencyLength k.val ^ 12) (p := 1)
      (by positivity) (higher_weight_pos k) (by norm_num)
      (fourierIsometry 12 u k.val) (fourierCoeff (firstShellTilt t) k.val)
    have he : (1 : ℝ) ^ 2 / (4 * (1 / (2 * D))) = D / 2 := by field_simp; ring
    rw [he] at h
    simpa only [one_mul, weightedSquare, ← Bridge.frequencyLength_eq,
      localQsigmaTerm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have h := hl.summable.tsum_le_tsum hpoint hr.summable
  rw [hl.tsum_eq, hr.tsum_eq] at h
  simpa only [localQsigma, one_div, div_eq_mul_inv, mul_comm, one_mul] using h

#print axioms higher_pairing_quadratic_bound
#print axioms higher_real_sq_integral_le_energy
end BecknerOnofri.HighDim
