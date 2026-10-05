module

public import BecknerOnofri.EntropyHeatIntegerEnclosure
public import BecknerOnofri.EntropyHeatFastPanelCertificate

@[expose] public section

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate

def SmallEndpoint.scaledPoint (p : SmallEndpoint) : ℤ := ⌊p.point*endpointPrecision⌋

def SmallEndpoint.integerCheck (p : SmallEndpoint) : Bool := decide (
  0 < p.scaledPoint ∧ p.point = fixedValue p.scaledPoint ∧
  0 ≤ p.directExp.lower ∧ 0 ≤ p.modularExp.upper ∧
  integerUpperPower p.modularExp.upper 5 < (endpointPrecision : ℤ) ∧
  p.directExp.argument = p.point ∧ p.modularExp.argument ≤ piLower^2/p.point ∧
  fixedValue (integerSmallBound p.scaledPoint p.directExp.lower p.modularExp.upper) ≤ p.upper)

theorem fixedValue_nonneg {a : ℤ} (ha : 0 ≤ a) : 0 ≤ fixedValue a := by
  unfold fixedValue
  positivity

theorem fixedValue_pos {a : ℤ} (ha : 0 < a) : 0 < fixedValue a := by
  unfold fixedValue
  have hP : (0 : ℚ) < endpointPrecision := by norm_num [endpointPrecision]
  exact div_pos (by exact_mod_cast ha) hP

theorem fixedValue_lt_one {a : ℤ} (ha : a < (endpointPrecision : ℤ)) : fixedValue a < 1 := by
  unfold fixedValue
  apply (div_lt_one (by norm_num [endpointPrecision] : (0 : ℚ) < endpointPrecision)).mpr
  exact_mod_cast ha

theorem SmallEndpoint.sound_integer (p : SmallEndpoint) (hc : p.integerCheck = true)
    (hd : p.directExp.Valid) (hm : p.modularExp.Valid) :
    heatComplement (p.point : ℝ) ≤ (p.upper : ℝ) := by
  have h : 0 < p.scaledPoint ∧ p.point = fixedValue p.scaledPoint ∧
      0 ≤ p.directExp.lower ∧ 0 ≤ p.modularExp.upper ∧
      integerUpperPower p.modularExp.upper 5 < (endpointPrecision : ℤ) ∧
      p.directExp.argument = p.point ∧ p.modularExp.argument ≤ piLower^2/p.point ∧
      fixedValue (integerSmallBound p.scaledPoint p.directExp.lower p.modularExp.upper) ≤ p.upper :=
    of_decide_eq_true hc
  obtain ⟨hs, heq, hL, hq, hq5, he, harg, hU⟩ := h
  have hs' : 0 < p.point := by rw [heq]; exact fixedValue_pos hs
  have hL' : 0 ≤ p.directExp.lowerBound := fixedValue_nonneg hL
  have hq' : 0 ≤ p.modularExp.upperBound := fixedValue_nonneg hq
  have hq5' : upperPower p.modularExp.upperBound 5 < 1 := by
    change upperPower (fixedValue p.modularExp.upper) 5 < 1
    rw [upperPower_fixed]
    exact fixedValue_lt_one hq5
  have hU' : smallRounded p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper := by
    change smallRounded p.point (fixedValue p.directExp.lower) (fixedValue p.modularExp.upper) ≤ p.upper
    rw [heq, smallRounded_fixed _ _ _ hs hq5]
    exact hU
  apply p.sound_fast _ hd hm
  exact decide_eq_true (show 0 < p.point ∧ 0 ≤ p.directExp.lowerBound ∧ 0 ≤ p.modularExp.upperBound ∧
    upperPower p.modularExp.upperBound 5 < 1 ∧ p.directExp.argument = p.point ∧
    p.modularExp.argument ≤ piLower^2/p.point ∧
    smallRounded p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper from
      ⟨hs', hL', hq', hq5', he, harg, hU'⟩)

def LargeEndpoint.integerCheck (p : LargeEndpoint) : Bool := decide (
  0 < p.point ∧ p.e11.upper < (endpointPrecision : ℤ) ∧
  p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
  p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
  p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
  fixedValue (integerDirectBound p.e1.upper p.e4.upper p.e9.upper p.e16.upper p.e25.upper p.e11.upper) ≤ p.upper)

theorem LargeEndpoint.sound_integer (p : LargeEndpoint) (hc : p.integerCheck = true)
    (h1 : p.e1.Valid) (h4 : p.e4.Valid) (h9 : p.e9.Valid)
    (h16 : p.e16.Valid) (h25 : p.e25.Valid) (h11 : p.e11.Valid) :
    heatComplement (p.point : ℝ) ≤ (p.upper : ℝ) := by
  have h : 0 < p.point ∧ p.e11.upper < (endpointPrecision : ℤ) ∧
      p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
      p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
      p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
      fixedValue (integerDirectBound p.e1.upper p.e4.upper p.e9.upper p.e16.upper p.e25.upper p.e11.upper) ≤ p.upper :=
    of_decide_eq_true hc
  obtain ⟨hs, hlt, he1, he4, he9, he16, he25, he11, hU⟩ := h
  have hlt' : p.e11.upperBound < 1 := fixedValue_lt_one hlt
  have hU' : directRounded p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
      p.e25.upperBound p.e11.upperBound ≤ p.upper := by
    change directRounded (fixedValue p.e1.upper) (fixedValue p.e4.upper) (fixedValue p.e9.upper)
      (fixedValue p.e16.upper) (fixedValue p.e25.upper) (fixedValue p.e11.upper) ≤ p.upper
    rw [directRounded_fixed _ _ _ _ _ _ hlt]
    exact hU
  apply p.sound_fast _ h1 h4 h9 h16 h25 h11
  exact decide_eq_true (show 0 < p.point ∧ p.e11.upperBound < 1 ∧
    p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
    p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
    p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
    directRounded p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
      p.e25.upperBound p.e11.upperBound ≤ p.upper from
        ⟨hs, hlt', he1, he4, he9, he16, he25, he11, hU'⟩)

#print axioms SmallEndpoint.sound_integer
#print axioms LargeEndpoint.sound_integer
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
