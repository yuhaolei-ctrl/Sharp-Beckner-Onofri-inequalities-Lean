import BecknerOnofri.SpectralSlice
import BecknerOnofri.SpectralSliceBase

noncomputable section
open scoped BigOperators

namespace BecknerOnofri.SpectralSlice

theorem even_integer_sum {f : ℤ → ℝ} (hf : Function.Even f) (hs : Summable f) :
    (∑' n : ℤ, f n) = f 0 + 2 * ∑' n : ℕ, f ((n : ℤ) + 1) := by
  have hnat : Summable (fun n : ℕ => f (n : ℤ)) := hs.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hs.comp_injective (show Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) by
      intro n m h
      change -((n : ℤ) + 1) = -((m : ℤ) + 1) at h
      omega)
  have hnegative : (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ, f ((n : ℤ) + 1) :=
    tsum_congr (fun n => hf ((n : ℤ) + 1))
  have hwhole : (∑' n : ℤ, f n) =
      (∑' n : ℕ, f (n : ℤ)) + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
    tsum_of_nat_of_neg_add_one hnat hneg
  rw [hwhole, hnegative, hnat.tsum_eq_zero_add]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem term_twelve_sqrt_two (n : ℤ) :
    term 12 (Real.sqrt 2) n = ((1 + (n : ℝ) ^ 2 / 2) ^ 6)⁻¹ := by
  unfold term
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show -(12 : ℝ) / 2 = -(6 : ℝ) by norm_num, Real.rpow_neg (by positivity)]
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem phi_twelve_sqrt_two_bound : phi 12 (Real.sqrt 2) ≤ (311141 / 342144 : ℝ) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have he : Function.Even (term 12 (Real.sqrt 2)) := by
    intro n
    simp [term, neg_div, neg_sq]
  have hs := even_integer_sum he (summable_term (by norm_num : (2 : ℝ) ≤ 12) hsqrt)
  have hnat (n : ℕ) : term 12 (Real.sqrt 2) ((n : ℤ) + 1) =
      HighDim.spectralSliceBaseTerm (n + 1) := by
    rw [term_twelve_sqrt_two]
    simp [HighDim.spectralSliceBaseTerm]
  rw [phi, hs]
  simp_rw [hnat]
  have hz : term 12 (Real.sqrt 2) 0 = 1 := by simp [term]
  rw [hz]
  have hi : (Real.sqrt 2)⁻¹ ≤ (3 / 4 : ℝ) := by
    have hroot : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
      Real.le_sqrt_of_sq_le (by norm_num)
    exact (inv_le_comm₀ (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)).mpr
      (by norm_num; exact hroot)
  calc
    _ ≤ (3 / 4 : ℝ) * (1 + 2 * ∑' n : ℕ, HighDim.spectralSliceBaseTerm (n + 1)) :=
      mul_le_mul_of_nonneg_right hi (by
        have hnonneg : 0 ≤ ∑' n : ℕ, HighDim.spectralSliceBaseTerm (n + 1) :=
          tsum_nonneg (fun _ => by unfold HighDim.spectralSliceBaseTerm; positivity)
        positivity)
    _ ≤ _ := HighDim.spectral_slice_base_bound

/-- The source's uniform spectral-slice estimate, for all real exponents p≥12. -/
theorem phi_bound {p a : ℝ} (hp : 12 ≤ p) (ha : Real.sqrt 2 ≤ a) :
    phi p a ≤ (311141 / 342144 : ℝ) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  exact (phi_antitone_exponent (by norm_num : (2 : ℝ) ≤ 12) hp (hsqrt.trans ha)).trans
    ((phi_antitone_radius (by norm_num : (2 : ℝ) ≤ 12) hsqrt ha).trans
      phi_twelve_sqrt_two_bound)

theorem spectral_slice_bound {p a : ℝ} (hp : 12 ≤ p) (ha : Real.sqrt 2 ≤ a) :
    a ^ (p - 1) * (∑' n : ℤ, (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2)) ≤
      (311141 / 342144 : ℝ) := by
  rw [← phi_rescale ((Real.sqrt_pos.mpr (by norm_num)).trans_le ha)]
  exact phi_bound hp ha

/-- Finite squared-radius form used by the face-deletion argument. -/
theorem finite_slice {p q : ℝ} (hp : 12 ≤ p) (hq : 4 ≤ q) (R : ℕ) :
    (∑ n ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (q + (n : ℝ) ^ 2) ^ (-p / 2)) ≤
      q ^ (-((p - 1) / 2)) := by
  let a : ℝ := Real.sqrt q
  have hq0 : 0 < q := by linarith
  have ha0 : 0 < a := Real.sqrt_pos.mpr hq0
  have hasq : a ^ 2 = q := Real.sq_sqrt hq0.le
  have hsqrt : Real.sqrt 2 ≤ a := Real.sqrt_le_sqrt (by linarith)
  have ha1 : 1 ≤ a := Real.le_sqrt_of_sq_le (by linarith)
  have hp2 : 2 ≤ p := by linarith
  let S := ∑' n : ℤ, (a ^ 2 + (n : ℝ) ^ 2) ^ (-p / 2)
  have hslice : a ^ (p - 1) * S < 1 :=
    (spectral_slice_bound hp hsqrt).trans_lt HighDim.spectral_slice_base_bound_lt_one
  have hfinite :
      (∑ n ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (q + (n : ℝ) ^ 2) ^ (-p / 2)) ≤ S := by
    have h := (summable_radial hp2 ha1).sum_le_tsum (Finset.Icc (-(R : ℤ)) (R : ℤ))
      (fun n _ => Real.rpow_nonneg (by positivity) (-p / 2))
    simpa only [S, hasq] using h
  have he : q ^ (-((p - 1) / 2)) = a ^ (-(p - 1)) := by
    rw [← hasq, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    congr 1
    ring
  have hproduct : a ^ (p - 1) * q ^ (-((p - 1) / 2)) = 1 := by
    rw [he, ← Real.rpow_add ha0, add_neg_cancel, Real.rpow_zero]
  have hpos := Real.rpow_pos_of_pos ha0 (p - 1)
  nlinarith

#print axioms spectral_slice_bound
#print axioms finite_slice

end BecknerOnofri.SpectralSlice
