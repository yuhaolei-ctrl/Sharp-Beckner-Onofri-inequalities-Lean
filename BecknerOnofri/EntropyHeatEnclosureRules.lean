import BecknerOnofri.EntropyHeatGlobal

/-! Analytic soundness rules for the numerical theta enclosures. Actual
certificate values must separately satisfy every premise. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.ThetaDomination

theorem exp_negative_nat (t : ℝ) (n : ℕ) :
    Real.exp (-(n : ℝ)*t) = Real.exp (-t)^n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem geometric_fourth_tail_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    a^4/(1-a^5) ≤ b^4/(1-b^5) := by
  have hb0 := ha.trans hab
  have hp : b^5 < 1 := pow_lt_one₀ hb0 hb (by norm_num)
  have hden : 0 < 1-b^5 := by linarith
  have hpow := pow_le_pow_left₀ ha hab 5
  exact (div_le_div_of_nonneg_left (pow_nonneg ha _) hden (by linarith)).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab 4) hden.le)

theorem theta_geometric_enclosure {t q : ℝ} (ht : 0 < t)
    (hq : Real.exp (-t) ≤ q) (hq1 : q < 1) :
    realTheta t ≤ 1+2*q+2*q^4/(1-q^5) := by
  have h := theta_cube_remainder ht
  have h4 : Real.exp (-4*t) = Real.exp (-t)^4 := by simpa using exp_negative_nat t 4
  have h5 : Real.exp (-5*t) = Real.exp (-t)^5 := by simpa using exp_negative_nat t 5
  rw [h4, h5, mul_div_assoc] at h
  have hg := geometric_fourth_tail_mono (Real.exp_pos (-t)).le hq hq1
  rw [mul_div_assoc]
  linarith

theorem modular_heat_enclosure {s p q L : ℝ} (hs : 0 < s)
    (hp : Real.pi ≤ p) (hq : Real.exp (-(Real.pi^2/s)) ≤ q) (hq1 : q < 1)
    (hL0 : 0 ≤ L) (hL : L ≤ Real.exp (-s)) :
    heatComplement s ≤
      (p/s)^6*(1+2*q+2*q^4/(1-q^5))^12-(1+2*L)^12 := by
  have ht : 0 < Real.pi^2/s := by positivity
  have hθ := theta_geometric_enclosure ht hq hq1
  have hθ0 : 0 ≤ realTheta (Real.pi^2/s) := zero_le_one.trans (one_le_realTheta ht)
  have htop := pow_le_pow_left₀ hθ0 hθ 12
  have hp0 : 0 < p := Real.pi_pos.trans_le hp
  have hscale : (Real.pi/s)^6 ≤ (p/s)^6 :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hp hs.le) 6
  have hm := mul_le_mul hscale htop (pow_nonneg hθ0 _) (by positivity : 0 ≤ (p/s)^6)
  have hlow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+2*L)
    (show 1+2*L ≤ 1+2*Real.exp (-s) by linarith) 12
  have hj : (realTheta s)^12 = (Real.pi/s)^6*(realTheta (Real.pi^2/s))^12 := by
    rw [SpectralSlice.theta_jacobi hs, mul_pow]
    congr 1
    rw [show (Real.sqrt (Real.pi/s))^12 = ((Real.sqrt (Real.pi/s))^2)^6 by ring,
      Real.sq_sqrt (by positivity)]
  change (realTheta s)^12-(1+2*Real.exp (-s))^12 ≤ _
  rw [hj]
  linarith

theorem power_difference_expansion (a b : ℝ) :
    (a+b)^12-a^12 = ∑ j ∈ Finset.range 12,
      (Nat.choose 12 (j+1) : ℝ)*a^(11-j)*b^(j+1) := by
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

theorem power_difference_mono {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haA : a ≤ A) (hbB : b ≤ B) : (a+b)^12-a^12 ≤ (A+B)^12-A^12 := by
  rw [power_difference_expansion, power_difference_expansion]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha haA _) (Nat.cast_nonneg _)
  · exact pow_le_pow_left₀ hb hbB _
  · exact pow_nonneg hb _
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ha.trans haA) _)

theorem direct_heat_enclosure {s E E4 E9 E16 E25 E11 : ℝ} (hs : 0 < s)
    (hE : Real.exp (-s) ≤ E)
    (h4 : Real.exp (-4*s) ≤ E4) (h9 : Real.exp (-9*s) ≤ E9)
    (h16 : Real.exp (-16*s) ≤ E16) (h25 : Real.exp (-25*s) ≤ E25)
    (h11 : Real.exp (-11*s) ≤ E11) (h11lt : E11 < 1) :
    heatComplement s ≤
      (1+2*E+(2*(E4+E9+E16)+2*E25/(1-E11)))^12-(1+2*E)^12 := by
  have hden : 0 < 1-E11 := by linarith
  have hden' : 0 < 1-Real.exp (-11*s) := by linarith
  have hfrac : Real.exp (-25*s)/(1-Real.exp (-11*s)) ≤ E25/(1-E11) := by
    exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hden (by linarith)).trans
      (div_le_div_of_nonneg_right h25 hden.le)
  have ht : realTheta s-(1+2*Real.exp (-s)) ≤ 2*(E4+E9+E16)+2*E25/(1-E11) := by
    have h := theta_four_remainder hs
    rw [mul_div_assoc] at h ⊢
    linarith
  have hb : 0 ≤ realTheta s-(1+2*Real.exp (-s)) := sub_nonneg.mpr (theta_cube_lower hs)
  have h := power_difference_mono (by positivity : (0 : ℝ) ≤ 1+2*Real.exp (-s)) hb
    (show 1+2*Real.exp (-s) ≤ 1+2*E by linarith) ht
  have heq : (1+2*Real.exp (-s)) + (realTheta s-(1+2*Real.exp (-s))) = realTheta s := by ring
  rw [heq] at h
  exact h

#print axioms modular_heat_enclosure
#print axioms direct_heat_enclosure
end BecknerOnofri.HighDim.EntropyTail
