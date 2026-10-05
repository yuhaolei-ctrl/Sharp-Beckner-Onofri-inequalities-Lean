import BecknerOnofri.LocalHighShell
import BecknerOnofri.CenteredExponential
import Mathlib.Algebra.Order.Chebyshev

/-! The actual higher-shell Qσ estimate in dimension twelve. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim

lemma higher_radiusSq_ge_two {d : ℕ} (k : HigherFrequency d) : 2 ≤ localRadiusSq k.val := by
  have hk : (1 : ℤ) < ∑ i : Fin d, (k.val i) ^ 2 := by
    have h := k.property
    unfold localRadiusSq at h
    exact_mod_cast h
  have hh : (2 : ℤ) ≤ ∑ i : Fin d, (k.val i) ^ 2 := by omega
  unfold localRadiusSq
  exact_mod_cast hh

lemma higher_inverse_twelfth_le (k : HigherFrequency 12) :
    (frequencyLength k.val ^ 12)⁻¹ ≤ (1 / 64 : ℝ) := by
  have hk := higher_radiusSq_ge_two k
  have hp : 0 ≤ localRadiusSq k.val := by linarith
  have he : frequencyLength k.val ^ 12 = localRadiusSq k.val ^ 6 := by
    change (Real.sqrt (localRadiusSq k.val)) ^ 12 = _
    calc
      _ = ((Real.sqrt (localRadiusSq k.val)) ^ 2) ^ 6 := by ring
      _ = _ := by rw [Real.sq_sqrt hp]
  rw [he]
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk 6
  norm_num at hh
  exact (inv_anti₀ (by norm_num) hh).trans_eq (by norm_num)

def localQsigmaTerm (t : Fin 12 → ℝ) (k : HigherFrequency 12) : ℝ :=
  (frequencyLength k.val ^ 12)⁻¹ * ‖fourierCoeff (firstShellTilt t) k.val‖ ^ 2

def localQsigma (t : Fin 12 → ℝ) : ℝ := ∑' k : HigherFrequency 12, localQsigmaTerm t k

lemma localQsigmaTerm_nonneg (t : Fin 12 → ℝ) (k : HigherFrequency 12) :
    0 ≤ localQsigmaTerm t k := by
  unfold localQsigmaTerm frequencyLength
  positivity

lemma localQsigmaTerm_le (t : Fin 12 → ℝ) (ht : ∀ i, 0 ≤ t i) (k : HigherFrequency 12) :
    localQsigmaTerm t k ≤ (1 / 64 : ℝ) * firstShellFourierMajorant t k.val :=
  mul_le_mul (higher_inverse_twelfth_le k) (firstShellTilt_fourier_sq_bound t ht k.val)
    (sq_nonneg _) (by norm_num)

lemma localQsigma_summable (t : Fin 12 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Summable (localQsigmaTerm t) :=
  Summable.of_nonneg_of_le (localQsigmaTerm_nonneg t) (localQsigmaTerm_le t ht)
    (((firstShellFourierMajorant_summable t).subtype _).mul_left (1 / 64))

lemma localQsigma_exponential_bound (t : Fin 12 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    localQsigma t ≤ (1 / 64 : ℝ) *
      (Real.exp (2 * ∑ i, t i ^ 2) - 1 - 2 * ∑ i, t i ^ 2) := by
  calc
    _ ≤ ∑' k : HigherFrequency 12, (1 / 64 : ℝ) * firstShellFourierMajorant t k.val :=
      (localQsigma_summable t ht).tsum_le_tsum (localQsigmaTerm_le t ht)
        (((firstShellFourierMajorant_summable t).subtype _).mul_left (1 / 64))
    _ = (1 / 64 : ℝ) * ∑' k : HigherFrequency 12, firstShellFourierMajorant t k.val := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (firstShellFourierMajorant_higher_bound t) (by norm_num)

lemma localQsigma_quartic_bound (t : Fin 12 → ℝ) (ht : ∀ i, 0 ≤ t i) :
    localQsigma t ≤ (3 / 8 : ℝ) * Real.exp (2 * ∑ i, t i ^ 2) * ∑ i, t i ^ 4 := by
  let A : ℝ := ∑ i, t i ^ 2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hexp := exp_le_quadratic_of_abs_le (x := 2 * A) (C := 2 * A)
    (by positivity) (by rw [abs_of_nonneg (by positivity)])
  have hsum : A ^ 2 ≤ 12 * ∑ i : Fin 12, t i ^ 4 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 12 => t i ^ 2)
    norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
    simpa only [← pow_mul] using h
  have hbound := localQsigma_exponential_bound t ht
  change localQsigma t ≤ 1 / 64 * (Real.exp (2 * A) - 1 - 2 * A) at hbound
  have hscale := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (2 * A)).le
  change localQsigma t ≤ 3 / 8 * Real.exp (2 * A) * ∑ i, t i ^ 4
  nlinarith

#print axioms localQsigma_quartic_bound
end BecknerOnofri.HighDim
