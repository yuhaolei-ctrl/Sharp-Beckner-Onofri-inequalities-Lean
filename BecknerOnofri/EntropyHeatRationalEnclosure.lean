import BecknerOnofri.EntropyHeatEnclosureRules
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact rational endpoint expressions and their analytic soundness. -/
noncomputable section
namespace BecknerOnofri.HighDim.EntropyTail

namespace HeatCertificate

def piLower : ℚ := 314159265358979323846 / 10^20
def piUpper : ℚ := 314159265358979323847 / 10^20

def smallUpper (s L q : ℚ) : ℚ :=
  (piUpper/s)^6*(1+2*q+2*q^4/(1-q^5))^12-(1+2*L)^12

def directUpper (E E4 E9 E16 E25 E11 : ℚ) : ℚ :=
  (1+2*E+(2*(E4+E9+E16)+2*E25/(1-E11)))^12-(1+2*E)^12

theorem smallUpper_sound (s L qarg q U : ℚ)
    (hs : 0 < s) (hL0 : 0 ≤ L) (hq1 : q < 1)
    (harg : qarg ≤ piLower^2/s) (hU : smallUpper s L q ≤ U)
    (hL : (L : ℝ) ≤ Real.exp (-(s : ℝ)))
    (hq : Real.exp (-(qarg : ℝ)) ≤ (q : ℝ)) :
    heatComplement (s : ℝ) ≤ (U : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hpiL : (piLower : ℝ) ≤ Real.pi := by
    have hp := Real.pi_gt_d20.le
    norm_num [piLower] at hp ⊢
    exact hp
  have hpiU : Real.pi ≤ (piUpper : ℝ) := by
    have hp := Real.pi_lt_d20.le
    norm_num [piUpper] at hp ⊢
    exact hp
  have hpiL0 : (0 : ℝ) ≤ piLower := by norm_num [piLower]
  have harg' : (qarg : ℝ) ≤ Real.pi^2/(s : ℝ) := by
    have ha : (qarg : ℝ) ≤ (piLower : ℝ)^2/(s : ℝ) := by exact_mod_cast harg
    exact ha.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ hpiL0 hpiL 2) hs'.le)
  have hq' : Real.exp (-(Real.pi^2/(s : ℝ))) ≤ (q : ℝ) :=
    (Real.exp_le_exp.mpr (neg_le_neg harg')).trans hq
  have ht := modular_heat_enclosure hs' hpiU hq'
    (by exact_mod_cast hq1) (by exact_mod_cast hL0) hL
  have heq : ((smallUpper s L q : ℚ) : ℝ) =
      ((piUpper : ℝ)/(s : ℝ))^6*(1+2*(q : ℝ)+2*(q : ℝ)^4/(1-(q : ℝ)^5))^12-
        (1+2*(L : ℝ))^12 := by
    simp only [smallUpper, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
      Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  rw [← heq] at ht
  exact ht.trans (by exact_mod_cast hU)

theorem directUpper_sound (s E E4 E9 E16 E25 E11 U : ℚ)
    (hs : 0 < s) (h11lt : E11 < 1) (hU : directUpper E E4 E9 E16 E25 E11 ≤ U)
    (hE : Real.exp (-(s : ℝ)) ≤ (E : ℝ))
    (h4 : Real.exp (-4*(s : ℝ)) ≤ (E4 : ℝ))
    (h9 : Real.exp (-9*(s : ℝ)) ≤ (E9 : ℝ))
    (h16 : Real.exp (-16*(s : ℝ)) ≤ (E16 : ℝ))
    (h25 : Real.exp (-25*(s : ℝ)) ≤ (E25 : ℝ))
    (h11 : Real.exp (-11*(s : ℝ)) ≤ (E11 : ℝ)) :
    heatComplement (s : ℝ) ≤ (U : ℝ) := by
  have ht := direct_heat_enclosure (by exact_mod_cast hs) hE h4 h9 h16 h25 h11
    (by exact_mod_cast h11lt)
  have heq : ((directUpper E E4 E9 E16 E25 E11 : ℚ) : ℝ) =
      (1+2*(E : ℝ)+(2*((E4 : ℝ)+(E9 : ℝ)+(E16 : ℝ))+2*(E25 : ℝ)/(1-(E11 : ℝ))))^12-
        (1+2*(E : ℝ))^12 := by
    simp only [directUpper, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
      Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  rw [← heq] at ht
  exact ht.trans (by exact_mod_cast hU)

#print axioms smallUpper_sound
#print axioms directUpper_sound
end HeatCertificate
end BecknerOnofri.HighDim.EntropyTail
