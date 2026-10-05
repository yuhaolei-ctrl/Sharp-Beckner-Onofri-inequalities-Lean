import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-! A quadratic right onset attached to a zero left phase has zero derivative. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

theorem zero_derivative_of_quadratic_onset {f : ℝ → ℝ} {a K C ε : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hC : 0 ≤ C) (hε : 0 < ε)
    (hzero : ∀ x ≤ a, f x = 0)
    (hbound : ∀ x, a < x → x < a+ε →
      |f x-K*(1-a/x)^2| ≤ C*(x-a)^3) : HasDerivAt f 0 a := by
  have hO : f =O[𝓝 a] (fun x => ‖x-a‖^2) := by
    apply IsBigO.of_bound (K/a^2+C)
    have hn : ∀ᶠ x in 𝓝 a, |x-a| < min ε 1 :=
      Metric.eventually_nhds_iff.mpr ⟨min ε 1,lt_min hε zero_lt_one,
        fun x hx => by simpa only [Real.dist_eq] using hx⟩
    filter_upwards [hn] with x hx
    simp only [Real.norm_eq_abs,abs_pow,abs_abs]
    by_cases hxa : x ≤ a
    · rw [hzero x hxa,abs_zero]
      positivity
    · have hax : a < x := lt_of_not_ge hxa
      have hx0 : 0 < x := ha.trans hax
      have hxε : x < a+ε := by have := (lt_min_iff.mp hx).1; linarith [le_abs_self (x-a)]
      have hx1 : x-a < 1 := by have := (lt_min_iff.mp hx).2; linarith [le_abs_self (x-a)]
      have ht : 0 ≤ x-a := sub_nonneg.mpr hax.le
      have hδ : 1-a/x = (x-a)/x := by field_simp
      have hδ0 : 0 ≤ 1-a/x := by rw [hδ]; positivity
      have hδle : 1-a/x ≤ (x-a)/a := by
        rw [hδ]
        exact div_le_div_of_nonneg_left ht ha hax.le
      have hsq : (1-a/x)^2 ≤ ((x-a)/a)^2 :=
        pow_le_pow_left₀ hδ0 hδle 2
      have hhigh := hbound x hax hxε
      have htri : |f x| ≤ |f x-K*(1-a/x)^2| + |K*(1-a/x)^2| := by
        have he : f x-K*(1-a/x)^2+K*(1-a/x)^2 = f x := by ring
        have h := abs_add_le (f x-K*(1-a/x)^2) (K*(1-a/x)^2)
        rwa [he] at h
      have hpow : (x-a)^3 ≤ (x-a)^2 := by nlinarith [sq_nonneg (x-a)]
      have hKsq := mul_le_mul_of_nonneg_left hsq hK
      have hCpow := mul_le_mul_of_nonneg_left hpow hC
      rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg _))] at htri
      rw [div_pow] at hKsq
      rw [sq_abs]
      calc
        _ ≤ C*(x-a)^3+K*(1-a/x)^2 := htri.trans (add_le_add hhigh le_rfl)
        _ ≤ C*(x-a)^2+K*((x-a)^2/a^2) := add_le_add hCpow hKsq
        _ = _ := by ring
  apply HasDerivAt.of_isLittleO
  simpa only [hzero a le_rfl,sub_zero,smul_zero] using
    hO.trans_isLittleO (isLittleO_pow_sub_sub a (by norm_num : 1 < 2))

#print axioms zero_derivative_of_quadratic_onset
end BecknerOnofri
