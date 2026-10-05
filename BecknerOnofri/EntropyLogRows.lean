import BecknerOnofri.EntropyLogEvaluator

namespace BecknerOnofri.HighDim.EntropyLogCertificate

def logPrecision : ℕ := 10^40

structure LogRow where
  value : ℚ
  numerator : ℤ
  denominator : ℤ
  shift : ℤ
  lower : ℚ
  upper : ℚ

def LogRow.check (c : LogRow) : Bool :=
  decide (0<c.denominator ∧ c.denominator≤c.numerator ∧ c.numerator≤2*c.denominator ∧
    c.value=((c.numerator : ℚ)/c.denominator)*2^c.shift ∧
    c.lower≤(integerScaled logPrecision c.numerator c.denominator c.shift 32).1 ∧
    (integerScaled logPrecision c.numerator c.denominator c.shift 32).2≤c.upper)

theorem LogRow.sound (c : LogRow) (hc : c.check=true) :
    (c.lower : ℝ)≤Real.log (c.value : ℝ) ∧ Real.log (c.value : ℝ)≤(c.upper : ℝ) := by
  have h := of_decide_eq_true hc
  obtain ⟨hb,hab,ha2b,hvalue,hlo,hup⟩ := h
  have hv : (c.value : ℝ)=((c.numerator : ℝ)/c.denominator)*2^c.shift := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_intCast, Rat.cast_zpow, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) hvalue
  rw [hv]
  have he := integerScaled_sound logPrecision (by norm_num [logPrecision])
    c.numerator c.denominator c.shift hb hab ha2b 32
  exact ⟨((Rat.cast_le (K := ℝ)).mpr hlo).trans he.1,
    he.2.trans ((Rat.cast_le (K := ℝ)).mpr hup)⟩

theorem logRows_sound (cs : List LogRow) (hc : cs.all LogRow.check=true)
    (i : Fin cs.length) :
    ((cs[i]).lower : ℝ)≤Real.log ((cs[i]).value : ℝ) ∧
      Real.log ((cs[i]).value : ℝ)≤((cs[i]).upper : ℝ) :=
  (cs[i]).sound (List.all_eq_true.mp hc _ (List.getElem_mem i.isLt))

#print axioms logRows_sound
end BecknerOnofri.HighDim.EntropyLogCertificate
