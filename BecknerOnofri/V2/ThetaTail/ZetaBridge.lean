module

public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.NumberTheory.ZetaValues
public import BecknerOnofri.V2.ThetaTail.RationalCertificates

@[expose] public section

/-! # Real-analytic soundness of the zeta certificates (Appendix B.1)

`zetaR p = ∑_{k≥1} k^{-p}` (as a real series, written over `k+1`), with
`zetaPartial p N ≤ zetaR p ≤ zetaUpper p N` for `p ≥ 2`, `N ≥ 1`.
(The Riemann zeta function itself is never needed: only these series.) -/
noncomputable section
open Finset Filter
namespace BecknerOnofri.V2.ThetaTail

/-- `∑_{k≥1} k^{-p}` -/
def zetaR (p : ℕ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ p

lemma summable_zetaTerm {p : ℕ} (hp : 2 ≤ p) : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ p) := by
  have h := (Real.summable_nat_pow_inv (p := p)).2 (by omega)
  have h2 := (summable_nat_add_iff 1).2 h
  refine h2.congr (fun k => ?_)
  simp [one_div]

lemma tele_ineq (q m : ℕ) (hq : 1 ≤ q) (hm : 1 ≤ m) :
    (q : ℝ) / ((m : ℝ) + 1) ^ (q + 1) ≤ 1 / (m : ℝ) ^ q - 1 / ((m : ℝ) + 1) ^ q := by
  have ha : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℝ := (m : ℝ) with hadef
  have hs : 0 < a ^ q := pow_pos ha q
  have ht : 0 < (a + 1) ^ q := pow_pos (by linarith) q
  have hb : 1 + (q : ℝ) * (1 / a) ≤ (1 + 1 / a) ^ q :=
    one_add_mul_le_pow (by have : 0 < 1 / a := by positivity
                           linarith) q
  have hdiv : (1 + 1 / a) ^ q = (a + 1) ^ q / a ^ q := by
    rw [← div_pow]; congr 1; field_simp
  rw [hdiv, le_div_iff₀ hs] at hb
  have key : (q : ℝ) * a ^ q / a ≤ (a + 1) ^ q - a ^ q := by
    have : (q : ℝ) * a ^ q / a = (q : ℝ) * (1 / a) * a ^ q := by field_simp
    nlinarith
  have h1 : (q : ℝ) * a ^ q / a / (a ^ q * (a + 1) ^ q) ≤ ((a + 1) ^ q - a ^ q) / (a ^ q * (a + 1) ^ q) :=
    div_le_div_of_nonneg_right key (by positivity)
  have e1 : (q : ℝ) * a ^ q / a / (a ^ q * (a + 1) ^ q) = (q : ℝ) / (a * (a + 1) ^ q) := by
    field_simp
  have e2 : ((a + 1) ^ q - a ^ q) / (a ^ q * (a + 1) ^ q) = 1 / a ^ q - 1 / (a + 1) ^ q := by
    field_simp
  have h3 : (q : ℝ) / ((a + 1) * (a + 1) ^ q) ≤ (q : ℝ) / (a * (a + 1) ^ q) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg q) (by positivity)
    nlinarith [pow_pos (show (0 : ℝ) < a + 1 by linarith) q]
  rw [e1, e2] at h1
  have e3 : (a + 1) ^ (q + 1) = (a + 1) * (a + 1) ^ q := by rw [pow_succ]; ring
  rw [e3]
  linarith

/-- telescoping bound on partial sums -/
lemma zeta_range_bound (q N n : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    ∑ k ∈ range (n + N), 1 / ((k : ℝ) + 1) ^ (q + 1)
      ≤ ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ (q + 1)
        + 1 / ((q : ℝ) * (N : ℝ) ^ q) - 1 / ((q : ℝ) * ((n + N : ℕ) : ℝ) ^ q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : 1 ≤ n + N := by omega
    have htel := tele_ineq q (n + N) hq hm
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have e : ∑ k ∈ range (n + 1 + N), 1 / ((k : ℝ) + 1) ^ (q + 1)
        = ∑ k ∈ range (n + N), 1 / ((k : ℝ) + 1) ^ (q + 1)
          + 1 / (((n + N : ℕ) : ℝ) + 1) ^ (q + 1) := by
      rw [show n + 1 + N = (n + N) + 1 by ring, sum_range_succ]
    rw [e]
    have e2 : 1 / (((n + N : ℕ) : ℝ) + 1) ^ (q + 1)
        ≤ 1 / ((q : ℝ) * ((n + N : ℕ) : ℝ) ^ q) - 1 / ((q : ℝ) * (((n + 1 + N : ℕ) : ℝ)) ^ q) := by
      have h1 : ((n + 1 + N : ℕ) : ℝ) = ((n + N : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [h1]
      have hm' : (0 : ℝ) < ((n + N : ℕ) : ℝ) := by exact_mod_cast hm
      have hh : 1 / (((n + N : ℕ) : ℝ) + 1) ^ (q + 1) = (1 / q) * ((q : ℝ) / (((n + N : ℕ) : ℝ) + 1) ^ (q + 1)) := by
        field_simp
      rw [hh]
      have e3 : 1 / ((q : ℝ) * ((n + N : ℕ) : ℝ) ^ q) - 1 / ((q : ℝ) * (((n + N : ℕ) : ℝ) + 1) ^ q)
          = (1 / q) * (1 / ((n + N : ℕ) : ℝ) ^ q - 1 / (((n + N : ℕ) : ℝ) + 1) ^ q) := by
        field_simp
      rw [e3]
      exact mul_le_mul_of_nonneg_left htel (by positivity)
    linarith

theorem zetaR_le (p N : ℕ) (hp : 2 ≤ p) (hN : 1 ≤ N) :
    zetaR p ≤ ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ p + 1 / (((p : ℝ) - 1) * (N : ℝ) ^ (p - 1)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : 1 ≤ q := by omega
  unfold zetaR
  refine Real.tsum_le_of_sum_range_le (fun k => by positivity) (fun n => ?_)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hmono : ∑ k ∈ range n, 1 / ((k : ℝ) + 1) ^ (q + 1)
      ≤ ∑ k ∈ range (n + N), 1 / ((k : ℝ) + 1) ^ (q + 1) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk; simp at hk ⊢; omega
    · intros; positivity
  have := zeta_range_bound q N n hq hN
  have hpos : 0 ≤ 1 / ((q : ℝ) * ((n + N : ℕ) : ℝ) ^ q) := by positivity
  have e : ((q + 1 : ℕ) : ℝ) - 1 = q := by push_cast; ring
  rw [e, show q + 1 - 1 = q from by omega]
  linarith

lemma sum_Icc_eq_range' (N : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Icc 1 N, f k = ∑ k ∈ range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem zetaPartial_le_zetaR (p N : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ p ≤ zetaR p :=
  (summable_zetaTerm hp).sum_le_tsum _ (fun k _ => by positivity)

/-- soundness of the zeta upper certificate -/
theorem zetaR_le_zetaUpper (p N : ℕ) (hp : 2 ≤ p) (hN : 1 ≤ N) :
    zetaR p ≤ ((zetaUpper p N : ℚ) : ℝ) := by
  have h := zetaR_le p N hp hN
  have e : ((zetaUpper p N : ℚ) : ℝ) =
      ∑ k ∈ range N, 1 / ((k : ℝ) + 1) ^ p + 1 / (((p : ℝ) - 1) * (N : ℝ) ^ (p - 1)) := by
    unfold zetaUpper zetaPartial
    push_cast
    congr 1
    · rw [sum_Icc_eq_range' N (fun k : ℕ => 1 / (k : ℝ) ^ p)]; push_cast; rfl
  rw [e]; exact h

theorem zetaR_two : zetaR 2 = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two
  have h2 := (hasSum_nat_add_iff' 1).2 h
  unfold zetaR
  simp only [range_one, sum_singleton] at h2
  simpa using h2.tsum_eq

theorem zetaR_four : zetaR 4 = Real.pi ^ 4 / 90 := by
  have h := hasSum_zeta_four
  have h2 := (hasSum_nat_add_iff' 1).2 h
  unfold zetaR
  simp only [range_one, sum_singleton] at h2
  simpa using h2.tsum_eq

theorem zetaR_six_lt : zetaR 6 < 101737 / 100000 := by
  have h := zetaR_le_zetaUpper 6 5 (by norm_num) (by norm_num)
  have h2 : ((zetaUpper 6 5 : ℚ) : ℝ) < ((101737 / 100000 : ℚ) : ℝ) := Rat.cast_lt.2 zeta6_upper
  push_cast at h2
  linarith

theorem zetaR_six_coeff_lt : 63 / 8 * zetaR 6 < 2003 / 250 := by
  have h := zetaR_six_lt
  have h2 : ((63 : ℚ) / 8 * (101737 / 100000) : ℚ) < ((2003 / 250 : ℚ) : ℝ) := by exact_mod_cast zeta6_coeff
  push_cast at h2
  linarith

theorem zetaR_five_lt : zetaR 5 < 1037 / 1000 := by
  have h := zetaR_le_zetaUpper 5 6 (by norm_num) (by norm_num)
  have h2 : ((zetaUpper 5 6 : ℚ) : ℝ) < ((1037 / 1000 : ℚ) : ℝ) := Rat.cast_lt.2 zeta5_upper
  push_cast at h2
  linarith

theorem zetaR_two_lt : zetaR 2 < 5 / 3 := by
  have h := zetaR_le_zetaUpper 2 5 (by norm_num) (by norm_num)
  have h2 : ((zetaUpper 2 5 : ℚ) : ℝ) < ((5 / 3 : ℚ) : ℝ) := Rat.cast_lt.2 zeta2_upper
  push_cast at h2
  linarith

theorem zetaR_four_gt : 27 / 25 < zetaR 4 := by
  have h := zetaPartial_le_zetaR 4 5 (by norm_num)
  have h2 : ((27 / 25 : ℚ) : ℝ) < ((zetaPartial 4 5 : ℚ) : ℝ) := Rat.cast_lt.2 zeta4_lower
  unfold zetaPartial at h2
  push_cast at h2
  rw [sum_Icc_eq_range' 5 (fun k : ℕ => 1 / (k : ℝ) ^ 4)] at h2
  push_cast at h2
  linarith

end BecknerOnofri.V2.ThetaTail
