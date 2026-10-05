import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
The exact positive-series definition of I₀(2t) and its quartic logarithmic bound.
The circle integral representation is proved separately in `BesselIntegral.lean`.
-/

noncomputable section
open scoped BigOperators

namespace BecknerOnofri.HighDim

def besselSeriesTerm (s : ℝ) (n : ℕ) : ℝ := s ^ n / (n.factorial : ℝ) ^ 2

def besselI0Two (t : ℝ) : ℝ := ∑' n : ℕ, t ^ (2 * n) / (n.factorial : ℝ) ^ 2

theorem besselSeriesTerm_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ besselSeriesTerm s n := by
  unfold besselSeriesTerm
  positivity

theorem besselSeries_summable {s : ℝ} (hs : 0 ≤ s) :
    Summable (besselSeriesTerm s) := by
  apply Summable.of_nonneg_of_le (besselSeriesTerm_nonneg hs)
    (fun n => ?_) (Real.summable_pow_div_factorial s)
  unfold besselSeriesTerm
  have hfac : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply div_le_div_of_nonneg_left (pow_nonneg hs n) (by positivity)
  nlinarith

theorem besselI0Two_summable (t : ℝ) :
    Summable (fun n : ℕ => t ^ (2 * n) / (n.factorial : ℝ) ^ 2) := by
  simp_rw [pow_mul]
  exact besselSeries_summable (sq_nonneg t)

theorem besselI0Two_eq_series (t : ℝ) :
    besselI0Two t = ∑' n : ℕ, besselSeriesTerm (t ^ 2) n := by
  simp only [besselI0Two, besselSeriesTerm, pow_mul]

theorem besselSeriesTerm_succ (s : ℝ) (n : ℕ) :
    besselSeriesTerm s (n + 1) = besselSeriesTerm s n * s / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  unfold besselSeriesTerm
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp

theorem besselSeries_tail_term_bound {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 25)
    (n : ℕ) : besselSeriesTerm s (n + 2) ≤ s ^ 2 / 4 * (1 / 225 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [besselSeriesTerm]
  | succ n ih =>
      have hden : (9 : ℝ) ≤ ((n + 2 + 1 : ℕ) : ℝ) ^ 2 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast
        nlinarith [sq_nonneg (n : ℝ)]
      have hdenpos : 0 < ((n + 2 + 1 : ℕ) : ℝ) ^ 2 := by linarith
      have hratio : s / ((n + 2 + 1 : ℕ) : ℝ) ^ 2 ≤ (1 / 225 : ℝ) := by
        apply (div_le_iff₀ hdenpos).2
        linarith
      calc
        besselSeriesTerm s (n + 1 + 2) =
            besselSeriesTerm s (n + 2) * (s / ((n + 2 + 1 : ℕ) : ℝ) ^ 2) := by
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, besselSeriesTerm_succ]
          ring
        _ ≤ (s ^ 2 / 4 * (1 / 225 : ℝ) ^ n) * (1 / 225 : ℝ) :=
          mul_le_mul ih hratio (div_nonneg hs hdenpos.le) (by positivity)
        _ = s ^ 2 / 4 * (1 / 225 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

theorem besselSeries_tail_bound {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 25) :
    (∑' n : ℕ, besselSeriesTerm s (n + 2)) ≤ (63 / 250 : ℝ) * s ^ 2 := by
  have hgeo : Summable (fun n : ℕ => (1 / 225 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have htail : Summable (fun n : ℕ => besselSeriesTerm s (n + 2)) :=
    (summable_nat_add_iff 2).mpr (besselSeries_summable hs)
  calc
    (∑' n : ℕ, besselSeriesTerm s (n + 2)) ≤
        ∑' n : ℕ, s ^ 2 / 4 * (1 / 225 : ℝ) ^ n :=
      htail.tsum_le_tsum (besselSeries_tail_term_bound hs hs') (hgeo.mul_left _)
    _ = s ^ 2 / 4 * (1 - (1 / 225 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num)]
    _ ≤ (63 / 250 : ℝ) * s ^ 2 := by nlinarith [sq_nonneg s]

theorem besselSeries_upper {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 25) :
    (∑' n : ℕ, besselSeriesTerm s n) ≤ 1 + s + (63 / 250 : ℝ) * s ^ 2 := by
  have hsplit := (besselSeries_summable hs).sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ, besselSeriesTerm] at hsplit
  have htail := besselSeries_tail_bound hs hs'
  unfold besselSeriesTerm at htail ⊢
  linarith

theorem one_le_besselI0Two (t : ℝ) : 1 ≤ besselI0Two t := by
  rw [besselI0Two_eq_series]
  have h := (besselSeries_summable (sq_nonneg t)).sum_le_tsum (Finset.range 1)
    (fun n _ => besselSeriesTerm_nonneg (sq_nonneg t) n)
  simpa [Finset.sum_range_succ, besselSeriesTerm] using h

theorem quartic_exponential_lower {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 25) :
    1 + s + (63 / 250 : ℝ) * s ^ 2 ≤ Real.exp (s - (6 / 25 : ℝ) * s ^ 2) := by
  let z : ℝ := s - (6 / 25 : ℝ) * s ^ 2
  have hsq : s ^ 2 ≤ s / 25 := by
    have h := mul_le_mul_of_nonneg_left hs' hs
    nlinarith
  have hzlower : 4 * s / 5 ≤ z := by dsimp [z]; nlinarith
  have hz : 0 ≤ z := le_trans (by positivity) hzlower
  have hcube : s ^ 3 / 2 ≤ z ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4 * s / 5) hzlower 3
    nlinarith [pow_nonneg hs 3]
  have hcubeupper : s ^ 3 ≤ s ^ 2 / 25 := by
    have h := mul_le_mul_of_nonneg_left hs' (sq_nonneg s)
    nlinarith
  have hzsq : z ^ 2 = s ^ 2 - (12 / 25 : ℝ) * s ^ 3 + (36 / 625 : ℝ) * s ^ 4 := by
    dsimp [z]
    ring
  have hexp := Real.sum_le_exp_of_nonneg hz 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  change 1 + s + (63 / 250 : ℝ) * s ^ 2 ≤ Real.exp z
  nlinarith [sq_nonneg (s ^ 2), sq_nonneg s]

theorem log_besselI0Two_quartic {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1 / 5) :
    Real.log (besselI0Two t) ≤ t ^ 2 - (6 / 25 : ℝ) * t ^ 4 := by
  have hs : t ^ 2 ≤ (1 / 25 : ℝ) := by
    have h := mul_self_le_mul_self ht ht'
    nlinarith
  apply (Real.log_le_iff_le_exp (lt_of_lt_of_le (by norm_num) (one_le_besselI0Two t))).2
  calc
    besselI0Two t = ∑' n : ℕ, besselSeriesTerm (t ^ 2) n := besselI0Two_eq_series t
    _ ≤ 1 + t ^ 2 + (63 / 250 : ℝ) * (t ^ 2) ^ 2 := besselSeries_upper (sq_nonneg t) hs
    _ ≤ Real.exp (t ^ 2 - (6 / 25 : ℝ) * (t ^ 2) ^ 2) :=
      quartic_exponential_lower (sq_nonneg t) hs
    _ = Real.exp (t ^ 2 - (6 / 25 : ℝ) * t ^ 4) := by congr 1; ring

end BecknerOnofri.HighDim
