module

public import BecknerOnofri.V2.ThetaTail.TailChain

@[expose] public section

/-! # The scalar tail bound `T_n ≤ R_n` (Lemma 5.13) — conditional on the twelve-square identity

All four boundary cases are kept explicit:

* `n = 0, 1`: both sides vanish (`Tn_eq_zero_of_le_one`, `Rn_eq_zero_of_le_one`) — unconditional;
* `n = 2`: `T_2 ≤ (1/6) e^{8/5} G(2/5) < 23/240 < 1/10 = R_2`;
* `n = 3`: `T_3 ≤ G(2/7) < 33/100 < 17/50 = R_3`;
* `n ≥ 4`: `T_n ≤ G(x) < U(x) < R_n` (`Ufun_lt_Rn`, via the degree-seven Bernstein polynomial).

The statements `*_of_twelveSquare` take `TwelveSquareIdentity` as hypothesis. -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.ThetaTail

lemma Hn_two : Hn 2 = 3 / 2 := by
  unfold Hn; simp [Finset.sum_Icc_succ_top]; norm_num

lemma Hn_three : Hn 3 = 11 / 6 := by
  unfold Hn; simp [Finset.sum_Icc_succ_top]; norm_num

lemma Hn_zero : Hn 0 = 0 := by unfold Hn; simp

lemma Hn_one : Hn 1 = 1 := by unfold Hn; simp

theorem Tn_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : Tn n = 0 := by
  unfold Tn
  have : (fun k : Fin 12 → ℤ =>
      (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * ∏ i, aCoef n (k i)) k)
      = fun _ => 0 := by
    funext k
    by_cases hk : k ∈ cube12ᶜ
    · rw [Set.indicator_of_mem hk]
      have hk' : k ∉ cube12 := hk
      rw [mem_cube12_iff] at hk'
      simp only [not_forall, not_or] at hk'
      obtain ⟨i, h1, h0, h2⟩ := hk'
      have hi : 2 ≤ (k i).natAbs := by omega
      have : aCoef n (k i) = 0 := by
        rw [aCoef_natAbs]; exact aCoef_eq_zero_of_lt n _ (by omega)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this, mul_zero]
    · rw [Set.indicator_of_notMem hk]
  rw [this, tsum_zero]

theorem Rn_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) : Rn n = 0 := by
  unfold Rn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · rw [Hn_zero, aCoef_one, aCoef_two, aCoef_three]; norm_num
  · rw [Hn_one, aCoef_one, aCoef_two, aCoef_three]; norm_num

theorem Rn_two : Rn 2 = 1 / 10 := by
  unfold Rn
  rw [Hn_two, aCoef_one, aCoef_two, aCoef_three]; norm_num

theorem Rn_three : Rn 3 = 17 / 50 := by
  unfold Rn
  rw [Hn_three, aCoef_one, aCoef_two, aCoef_three]; norm_num

theorem xn_two : xn 2 = 2 / 5 := by rw [xn_eq]; norm_num

theorem xn_three : xn 3 = 2 / 7 := by rw [xn_eq]; norm_num

theorem Tn_two_lt_Rn_of_twelveSquare (hT : TwelveSquareIdentity) : Tn 2 < Rn 2 := by
  have h1 := Tn_le_two_G 2
  rw [xn_two] at h1
  have hG := G_two_fifths_lt_of_twelveSquare hT
  have hG0 := G_nonneg (2 / 5)
  have ha : aCoef 2 2 = 1 / 6 := by rw [aCoef_two]; norm_num
  have he : Real.exp (4 * (2 / 5)) < 5 := by
    have := exp_lt_five_of_exp85
    rwa [show (4 : ℝ) * (2 / 5) = 8 / 5 by norm_num]
  rw [ha] at h1
  rw [Rn_two]
  have : 1 / 6 * Real.exp (4 * (2 / 5)) * G (2 / 5) ≤ 1 / 6 * 5 * (23 / 200) := by
    have : Real.exp (4 * (2 / 5)) * G (2 / 5) ≤ 5 * (23 / 200) :=
      mul_le_mul he.le hG.le hG0 (by norm_num)
    nlinarith
  linarith

theorem Tn_three_lt_Rn_of_twelveSquare (hT : TwelveSquareIdentity) : Tn 3 < Rn 3 := by
  have h1 := Tn_le_G 3
  rw [xn_three] at h1
  have hG := G_two_sevenths_lt_of_twelveSquare hT
  rw [Rn_three]
  linarith

theorem Tn_lt_Rn_of_four_le_of_twelveSquare (hT : TwelveSquareIdentity) {n : ℕ} (hn : 4 ≤ n) :
    Tn n < Rn n := by
  have h1 := Tn_le_G n
  have hx : xn n < 1 := by
    rw [xn_eq, div_lt_one (by positivity)]
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h2 := G_lt_U_of_twelveSquare hT (xn_pos n) hx
  have h3 := Ufun_lt_Rn hn
  linarith

/-- **Lemma 5.13 (scalar tail bound), conditional on the twelve-square identity**:
`T_n ≤ R_n` for every `n ≥ 0`. -/
theorem Tn_le_Rn_of_twelveSquare (hT : TwelveSquareIdentity) (n : ℕ) : Tn n ≤ Rn n := by
  by_cases h1 : n ≤ 1
  · rw [Tn_eq_zero_of_le_one h1, Rn_eq_zero_of_le_one h1]
  by_cases h2 : n = 2
  · subst h2; exact (Tn_two_lt_Rn_of_twelveSquare hT).le
  by_cases h3 : n = 3
  · subst h3; exact (Tn_three_lt_Rn_of_twelveSquare hT).le
  exact (Tn_lt_Rn_of_four_le_of_twelveSquare hT (by omega)).le

end BecknerOnofri.V2.ThetaTail
