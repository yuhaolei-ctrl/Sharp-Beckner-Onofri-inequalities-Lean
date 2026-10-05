import BecknerOnofri.EntropyExpCertificate
import BecknerOnofri.EntropyHeatRationalEnclosure

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate

def endpointPrecision : ℕ := 10^60

def upperPower (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => roundUp endpointPrecision (upperPower x n*x)

def lowerPower (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | n+1 => max 0 (roundDown endpointPrecision (lowerPower x n*x))

theorem power_le_upperPower {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : x^n ≤ upperPower x n := by
  induction n with
  | zero => simp [upperPower, lowerPower]
  | succ n ih =>
    rw [pow_succ, upperPower]
    exact (mul_le_mul_of_nonneg_right ih hx).trans
      (le_roundUp endpointPrecision (by norm_num [endpointPrecision]) _)

theorem lowerPower_le_power {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : lowerPower x n ≤ x^n := by
  induction n with
  | zero => simp [upperPower, lowerPower]
  | succ n ih =>
    rw [pow_succ, lowerPower]
    apply max_le (mul_nonneg (pow_nonneg hx _) hx)
    exact (roundDown_le endpointPrecision (by norm_num [endpointPrecision]) _).trans
      (mul_le_mul_of_nonneg_right ih hx)

def smallRounded (s L q : ℚ) : ℚ :=
  let r := roundUp endpointPrecision (piUpper/s)
  let t := 1+2*q+2*roundUp endpointPrecision (upperPower q 4/(1-upperPower q 5))
  roundUp endpointPrecision (upperPower r 6*upperPower t 12)-lowerPower (1+2*L) 12

theorem smallRounded_upper {s L q : ℚ} (hs : 0 < s) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (hq5 : upperPower q 5 < 1) : smallUpper s L q ≤ smallRounded s L q := by
  have hP : 0 < endpointPrecision := by norm_num [endpointPrecision]
  have h4 := power_le_upperPower hq 4
  have h5 := power_le_upperPower hq 5
  have hden : 0 < 1-upperPower q 5 := by linarith
  have hfrac : q^4/(1-q^5) ≤ upperPower q 4/(1-upperPower q 5) :=
    (div_le_div_of_nonneg_left (pow_nonneg hq 4) hden (by linarith)).trans
      (div_le_div_of_nonneg_right h4 hden.le)
  let t := 1+2*q+2*roundUp endpointPrecision (upperPower q 4/(1-upperPower q 5))
  have ht : 1+2*q+2*q^4/(1-q^5) ≤ t := by
    have h := hfrac.trans (le_roundUp endpointPrecision hP _)
    dsimp only [t]
    rw [mul_div_assoc]
    linarith
  have ht0 : 0 ≤ 1+2*q+2*q^4/(1-q^5) := by
    have hd : 0 < 1-q^5 := by linarith
    positivity
  have hratio0 : 0 ≤ piUpper/s := by unfold piUpper; positivity
  have hr := le_roundUp endpointPrecision hP (piUpper/s)
  have ht12 := (pow_le_pow_left₀ ht0 ht 12).trans (power_le_upperPower (ht0.trans ht) 12)
  have hr6 := (pow_le_pow_left₀ hratio0 hr 6).trans (power_le_upperPower (hratio0.trans hr) 6)
  have hm := mul_le_mul hr6 ht12 (pow_nonneg ht0 12)
    ((pow_nonneg (hratio0.trans hr) 6).trans (power_le_upperPower (hratio0.trans hr) 6))
  have hu := hm.trans (le_roundUp endpointPrecision hP _)
  have hl := lowerPower_le_power (by positivity : (0 : ℚ) ≤ 1+2*L) 12
  exact sub_le_sub hu hl

def directRounded (E E4 E9 E16 E25 E11 : ℚ) : ℚ :=
  let t := 2*(E4+E9+E16)+2*roundUp endpointPrecision (E25/(1-E11))
  upperPower (1+2*E+t) 12-lowerPower (1+2*E) 12

theorem directRounded_upper {E E4 E9 E16 E25 E11 : ℚ}
    (hE : 0 ≤ E) (h4 : 0 ≤ E4) (h9 : 0 ≤ E9) (h16 : 0 ≤ E16)
    (h25 : 0 ≤ E25) (h11 : E11 < 1) :
    directUpper E E4 E9 E16 E25 E11 ≤ directRounded E E4 E9 E16 E25 E11 := by
  have ht0 : 0 ≤ 1+2*E+(2*(E4+E9+E16)+2*E25/(1-E11)) := by
    have hd : 0 < 1-E11 := by linarith
    positivity
  have ht : 1+2*E+(2*(E4+E9+E16)+2*E25/(1-E11)) ≤
      1+2*E+(2*(E4+E9+E16)+2*roundUp endpointPrecision (E25/(1-E11))) := by
    have h := le_roundUp endpointPrecision (by norm_num [endpointPrecision]) (E25/(1-E11))
    rw [mul_div_assoc]
    linarith
  have hu := (pow_le_pow_left₀ ht0 ht 12).trans (power_le_upperPower (ht0.trans ht) 12)
  have hl := lowerPower_le_power (by positivity : (0 : ℚ) ≤ 1+2*E) 12
  exact sub_le_sub hu hl

#print axioms smallRounded_upper
#print axioms directRounded_upper
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
