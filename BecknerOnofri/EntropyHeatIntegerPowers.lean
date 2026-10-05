import BecknerOnofri.EntropyHeatRoundedPowers
import BecknerOnofri.EntropyExpInteger

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate

def fixedValue (a : ℤ) : ℚ := (a : ℚ)/endpointPrecision

def mulUp (a b : ℤ) : ℤ := ceilDiv (a*b) endpointPrecision
def mulDown (a b : ℤ) : ℤ := max 0 ((a*b)/endpointPrecision)
def divUp (a b : ℤ) : ℤ := ceilDiv (a*endpointPrecision) b

def integerUpperPower (a : ℤ) : ℕ → ℤ
  | 0 => endpointPrecision
  | n+1 => mulUp (integerUpperPower a n) a

def integerLowerPower (a : ℤ) : ℕ → ℤ
  | 0 => endpointPrecision
  | n+1 => mulDown (integerLowerPower a n) a

theorem roundUp_mul_fixed (a b : ℤ) :
    roundUp endpointPrecision (fixedValue a*fixedValue b) = fixedValue (mulUp a b) := by
  have h := roundUp_ratio endpointPrecision (by norm_num [endpointPrecision])
    (a*b) (endpointPrecision : ℤ) (by norm_num [endpointPrecision])
  convert h using 1 <;> simp only [fixedValue, mulUp, Int.cast_mul, Int.cast_natCast] <;> ring

theorem roundDown_mul_fixed (a b : ℤ) :
    max 0 (roundDown endpointPrecision (fixedValue a*fixedValue b)) = fixedValue (mulDown a b) := by
  have h := roundDown_ratio endpointPrecision (by norm_num [endpointPrecision])
    (a*b) (endpointPrecision : ℤ) (by norm_num [endpointPrecision])
  have he : fixedValue a*fixedValue b = ((a*b : ℤ) : ℚ)/
      (((endpointPrecision : ℤ) : ℚ)*endpointPrecision) := by
    simp only [fixedValue, Int.cast_mul, Int.cast_natCast]
    ring
  rw [he, h]
  simp only [fixedValue, mulDown, Int.cast_max, Int.cast_zero]
  simpa only [zero_div] using (max_div_div_right
    (by norm_num [endpointPrecision] : (0 : ℚ) ≤ endpointPrecision)
    (0 : ℚ) ((a*b/(endpointPrecision : ℤ) : ℤ) : ℚ))

theorem roundUp_div_fixed (a b : ℤ) (hb : 0 < b) :
    roundUp endpointPrecision (fixedValue a/fixedValue b) = fixedValue (divUp a b) := by
  have h := roundUp_ratio endpointPrecision (by norm_num [endpointPrecision])
    (a*endpointPrecision) b hb
  convert h using 1 <;> simp only [fixedValue, divUp, Int.cast_mul, Int.cast_natCast]
  have hP : (endpointPrecision : ℚ) ≠ 0 := by norm_num [endpointPrecision]
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp

theorem upperPower_fixed (a : ℤ) (n : ℕ) :
    upperPower (fixedValue a) n = fixedValue (integerUpperPower a n) := by
  induction n with
  | zero => norm_num [upperPower, integerUpperPower, fixedValue, endpointPrecision]
  | succ n ih => rw [upperPower, ih, roundUp_mul_fixed, integerUpperPower]

theorem lowerPower_fixed (a : ℤ) (n : ℕ) :
    lowerPower (fixedValue a) n = fixedValue (integerLowerPower a n) := by
  induction n with
  | zero => norm_num [lowerPower, integerLowerPower, fixedValue, endpointPrecision]
  | succ n ih => rw [lowerPower, ih, roundDown_mul_fixed, integerLowerPower]

#print axioms upperPower_fixed
#print axioms lowerPower_fixed
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
