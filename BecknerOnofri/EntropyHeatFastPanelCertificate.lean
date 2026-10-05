import BecknerOnofri.EntropyHeatRoundedPowers
import BecknerOnofri.EntropyHeatPanelCertificate

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate

def SmallEndpoint.fastCheck (p : SmallEndpoint) : Bool := decide (
  0 < p.point ∧ 0 ≤ p.directExp.lowerBound ∧ 0 ≤ p.modularExp.upperBound ∧
  upperPower p.modularExp.upperBound 5 < 1 ∧ p.directExp.argument = p.point ∧
  p.modularExp.argument ≤ piLower^2/p.point ∧
  smallRounded p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper)

theorem SmallEndpoint.sound_fast (p : SmallEndpoint) (hc : p.fastCheck = true)
    (hd : p.directExp.Valid) (hm : p.modularExp.Valid) :
    heatComplement (p.point : ℝ) ≤ (p.upper : ℝ) := by
  have h : 0 < p.point ∧ 0 ≤ p.directExp.lowerBound ∧ 0 ≤ p.modularExp.upperBound ∧
      upperPower p.modularExp.upperBound 5 < 1 ∧ p.directExp.argument = p.point ∧
      p.modularExp.argument ≤ piLower^2/p.point ∧
      smallRounded p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper :=
    of_decide_eq_true hc
  obtain ⟨hs, hL, hq, hq5, he, harg, hU⟩ := h
  have hq1 : p.modularExp.upperBound < 1 := by
    by_contra! hn
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1) hn 5
    norm_num only [one_pow] at hp
    have ht := power_le_upperPower hq 5
    linarith
  apply p.sound _ hd hm
  exact decide_eq_true (show 0 < p.point ∧ 0 ≤ p.directExp.lowerBound ∧
    p.modularExp.upperBound < 1 ∧ p.directExp.argument = p.point ∧
    p.modularExp.argument ≤ piLower^2/p.point ∧
    smallUpper p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper from
      ⟨hs, hL, hq1, he, harg, (smallRounded_upper hs hL hq hq5).trans hU⟩)

def LargeEndpoint.fastCheck (p : LargeEndpoint) : Bool := decide (
  0 < p.point ∧ p.e11.upperBound < 1 ∧
  p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
  p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
  p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
  directRounded p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
    p.e25.upperBound p.e11.upperBound ≤ p.upper)

theorem LargeEndpoint.sound_fast (p : LargeEndpoint) (hc : p.fastCheck = true)
    (h1 : p.e1.Valid) (h4 : p.e4.Valid) (h9 : p.e9.Valid)
    (h16 : p.e16.Valid) (h25 : p.e25.Valid) (h11 : p.e11.Valid) :
    heatComplement (p.point : ℝ) ≤ (p.upper : ℝ) := by
  have h : 0 < p.point ∧ p.e11.upperBound < 1 ∧
      p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
      p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
      p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
      directRounded p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
        p.e25.upperBound p.e11.upperBound ≤ p.upper := of_decide_eq_true hc
  obtain ⟨hs, hlt, he1, he4, he9, he16, he25, he11, hU⟩ := h
  have hn (e : Entry) (he : e.Valid) : 0 ≤ e.upperBound := by
    exact_mod_cast (Real.exp_pos _).le.trans he.2
  apply p.sound _ h1 h4 h9 h16 h25 h11
  exact decide_eq_true (show 0 < p.point ∧ p.e11.upperBound < 1 ∧
    p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
    p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
    p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
    directUpper p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
      p.e25.upperBound p.e11.upperBound ≤ p.upper from
      ⟨hs, hlt, he1, he4, he9, he16, he25, he11,
        (directRounded_upper (hn _ h1) (hn _ h4) (hn _ h9) (hn _ h16) (hn _ h25) hlt).trans hU⟩)

#print axioms SmallEndpoint.sound_fast
#print axioms LargeEndpoint.sound_fast
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
