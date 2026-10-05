module

public import BecknerOnofri.ElevenThetaIntegrability
public import Legacy.BecknerOnofri.ThetaPolynomialMajorant
public import Legacy.BecknerOnofri.ThetaExponentialIntegral

@[expose] public section

/-! The dimension-eleven theta certificate from Section 4. All infinite
series and improper integrals retain their mathematical meanings. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open Legacy.BecknerOnofri.ThetaDomination
open Legacy.BecknerOnofri.ThetaExponentialIntegral
namespace BecknerOnofri.HighDim.Eleven.ThetaBound

theorem geometric_mode (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Real.exp (-t * ((n+1 : ℕ) : ℝ)^2) ≤ Real.exp (-t) * Real.exp (-3*t)^n := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) n
  push_cast
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hn)]

theorem theta_geometric {t : ℝ} (ht : 0 < t) :
    realTheta t ≤ 1 + 2 * Real.exp (-t) / (1-Real.exp (-3*t)) := by
  have hnat : Summable (fun n : ℕ => Real.exp (-t * (n : ℝ)^2)) := by
    simpa only [Int.cast_natCast] using
      (summable_int_iff_summable_nat_and_neg.mp (summable_realTheta ht)).1
  have hs : Summable (fun n : ℕ => Real.exp (-t * ((n+1 : ℕ) : ℝ)^2)) :=
    (summable_nat_add_iff 1).mpr hnat
  have hq : Real.exp (-3*t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum := hs.tsum_le_tsum (geometric_mode t ht.le)
    ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left (Real.exp (-t)))
  rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hq] at hsum
  rw [realTheta_eq_one_add_two_mul_tsum ht]
  simp only [div_eq_mul_inv]
  linarith

theorem exp_neg_pi_lt : Real.exp (-Real.pi) < (433 : ℝ)/10000 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 157/50) 25
  have hpoly : (10000 : ℝ)/433 < ∑ j ∈ Finset.range 25, ((157 : ℝ)/50)^j / j.factorial := by
    norm_num [Finset.sum_range_succ]
  have he : (10000 : ℝ)/433 < Real.exp Real.pi :=
    (hpoly.trans_le h).trans (Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_d2]))
  rw [Real.exp_neg, ← one_div]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  linarith

theorem theta_uniform {r : ℝ} (hr : 1 ≤ r) :
    realTheta (Real.pi*r) ≤ 1 + (2 / (1-((433 : ℝ)/10000)^3)) * Real.exp (-Real.pi*r) := by
  have ht : 0 < Real.pi*r := mul_pos Real.pi_pos (zero_lt_one.trans_le hr)
  have hg := theta_geometric ht
  have hsmall : Real.exp (-3*(Real.pi*r)) ≤ ((433 : ℝ)/10000)^3 := by
    calc
      _ ≤ Real.exp (-3*Real.pi) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      _ = Real.exp (-Real.pi)^3 := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := by gcongr; exact exp_neg_pi_lt.le
  have hd : (0 : ℝ) < 1-((433 : ℝ)/10000)^3 := by norm_num
  have hfrac := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 2 * Real.exp (-(Real.pi*r))) hd (by linarith :
      1-((433 : ℝ)/10000)^3 ≤ 1-Real.exp (-3*(Real.pi*r)))
  have he : 2 * Real.exp (-(Real.pi*r)) / (1-((433 : ℝ)/10000)^3) =
      (2 / (1-((433 : ℝ)/10000)^3)) * Real.exp (-Real.pi*r) := by rw [neg_mul]; ring
  linarith

def laplacePolynomial (m : ℕ) (a : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ) * j.factorial / a^(j+1)

def rationalUpper : ℝ :=
  ∑ j ∈ Finset.range 11,
    ((11 : ℕ).choose (j+1) : ℝ) * (2*((433 : ℝ)/10000)/(1-((433 : ℝ)/10000)^3))^(j+1) *
      ((laplacePolynomial 4 ((j+1)*((157 : ℝ)/50)) +
        laplacePolynomial 5 ((j+1)*((157 : ℝ)/50)))/2 +
        laplacePolynomial 0 ((j+1)*((157 : ℝ)/50)))

theorem rationalUpper_lt : rationalUpper < (5 : ℝ)/2 := by
  norm_num [rationalUpper, laplacePolynomial, Finset.sum_range_succ, Nat.choose, Nat.factorial]

#print axioms theta_uniform
#print axioms rationalUpper_lt
end BecknerOnofri.HighDim.Eleven.ThetaBound
