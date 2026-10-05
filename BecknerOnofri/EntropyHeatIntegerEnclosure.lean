import BecknerOnofri.EntropyHeatIntegerPowers

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

def piUpperInteger : ℤ := 314159265358979323847*10^40

def integerSmallBound (s L q : ℤ) : ℤ :=
  let r := divUp piUpperInteger s
  let t := endpointPrecision+2*q+2*divUp (integerUpperPower q 4) (endpointPrecision-integerUpperPower q 5)
  mulUp (integerUpperPower r 6) (integerUpperPower t 12)-integerLowerPower (endpointPrecision+2*L) 12

def integerDirectBound (E E4 E9 E16 E25 E11 : ℤ) : ℤ :=
  let t := 2*(E4+E9+E16)+2*divUp E25 (endpointPrecision-E11)
  integerUpperPower (endpointPrecision+2*E+t) 12-integerLowerPower (endpointPrecision+2*E) 12

theorem fixedValue_sub (a b : ℤ) : fixedValue (a-b) = fixedValue a-fixedValue b := by
  simp only [fixedValue, Int.cast_sub]
  ring

theorem fixedValue_one : fixedValue endpointPrecision = 1 := by
  norm_num [fixedValue, endpointPrecision]

theorem fixedValue_base (a : ℤ) : fixedValue (endpointPrecision+2*a) = 1+2*fixedValue a := by
  simp only [fixedValue, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  have hP : (endpointPrecision : ℚ) ≠ 0 := by norm_num [endpointPrecision]
  field_simp

theorem smallRounded_fixed (s L q : ℤ) (hs : 0 < s)
    (hq : integerUpperPower q 5 < (endpointPrecision : ℤ)) :
    smallRounded (fixedValue s) (fixedValue L) (fixedValue q) =
      fixedValue (integerSmallBound s L q) := by
  have hpi : piUpper = fixedValue piUpperInteger := by norm_num [piUpper, fixedValue, piUpperInteger, endpointPrecision]
  have hr : ExpCertificate.roundUp endpointPrecision (piUpper/fixedValue s) =
      fixedValue (divUp piUpperInteger s) := by rw [hpi, roundUp_div_fixed _ _ hs]
  have hd : 0 < (endpointPrecision : ℤ)-integerUpperPower q 5 := by omega
  have hden : 1-upperPower (fixedValue q) 5 =
      fixedValue ((endpointPrecision : ℤ)-integerUpperPower q 5) := by
    rw [upperPower_fixed, fixedValue_sub, fixedValue_one]
  have ht : 1+2*fixedValue q+2*ExpCertificate.roundUp endpointPrecision
      (upperPower (fixedValue q) 4/(1-upperPower (fixedValue q) 5)) =
      fixedValue (endpointPrecision+2*q+2*divUp (integerUpperPower q 4)
        (endpointPrecision-integerUpperPower q 5)) := by
    rw [hden, upperPower_fixed, roundUp_div_fixed _ _ hd]
    simp only [fixedValue, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    have hP : (endpointPrecision : ℚ) ≠ 0 := by norm_num [endpointPrecision]
    field_simp
    <;> ring
  dsimp only [smallRounded]
  rw [hr, ht, upperPower_fixed, upperPower_fixed, roundUp_mul_fixed,
    ← fixedValue_base L, lowerPower_fixed, ← fixedValue_sub]
  rfl

theorem directRounded_fixed (E E4 E9 E16 E25 E11 : ℤ)
    (h11 : E11 < (endpointPrecision : ℤ)) :
    directRounded (fixedValue E) (fixedValue E4) (fixedValue E9)
      (fixedValue E16) (fixedValue E25) (fixedValue E11) =
      fixedValue (integerDirectBound E E4 E9 E16 E25 E11) := by
  have hd : 0 < (endpointPrecision : ℤ)-E11 := by omega
  have hden : 1-fixedValue E11 = fixedValue ((endpointPrecision : ℤ)-E11) := by
    rw [fixedValue_sub, fixedValue_one]
  have ht : 1+2*fixedValue E+(2*(fixedValue E4+fixedValue E9+fixedValue E16)+
      2*ExpCertificate.roundUp endpointPrecision (fixedValue E25/(1-fixedValue E11))) =
      fixedValue (endpointPrecision+2*E+(2*(E4+E9+E16)+2*divUp E25 (endpointPrecision-E11))) := by
    rw [hden, roundUp_div_fixed _ _ hd]
    simp only [fixedValue, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    have hP : (endpointPrecision : ℚ) ≠ 0 := by norm_num [endpointPrecision]
    field_simp
    <;> ring
  dsimp only [directRounded]
  rw [ht, upperPower_fixed, ← fixedValue_base E, lowerPower_fixed, ← fixedValue_sub]
  rfl

#print axioms smallRounded_fixed
#print axioms directRounded_fixed
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
