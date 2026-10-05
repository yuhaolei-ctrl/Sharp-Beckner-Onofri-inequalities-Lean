import BecknerOnofri.ScalarBesselInteger

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar

def besselPrecision : ℕ := 10^100

structure BesselRow where
  numerator : ℤ
  denominator : ℤ
  order : ℕ
  terms : ℕ
  lower : ℤ
  upper : ℤ

def BesselRow.check (c : BesselRow) : Bool :=
  let s := integerBessel besselPrecision c.numerator c.denominator c.order c.terms
  decide (0≤c.numerator ∧ 0<c.denominator ∧
    2*c.numerator^2≤(c.terms+1 : ℤ)^2*c.denominator^2 ∧
    c.lower=s.sumLower ∧ c.upper=s.sumUpper+2*s.termUpper)

theorem BesselRow.sound (c : BesselRow) (hc : c.check=true) :
    (c.lower : ℝ)/besselPrecision≤bessel c.order ((c.numerator : ℝ)/c.denominator) ∧
      bessel c.order ((c.numerator : ℝ)/c.denominator)≤(c.upper : ℝ)/besselPrecision := by
  have h := of_decide_eq_true hc
  obtain ⟨hn,hd,hscale,hl,hu⟩ := h
  have hp : 0<besselPrecision := by norm_num [besselPrecision]
  have hq : (0 : ℚ)≤(c.numerator : ℚ)/c.denominator := div_nonneg
    (by exact_mod_cast hn) (by exact_mod_cast hd.le)
  have hDq : (0 : ℚ)<c.denominator := by exact_mod_cast hd
  have hs : ((c.numerator : ℚ)/c.denominator)^2≤(1/2 : ℚ)*(c.terms+1)^2 := by
    have h : (2 : ℚ)*c.numerator^2≤(c.terms+1 : ℚ)^2*c.denominator^2 := by exact_mod_cast hscale
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hDq)).mpr
    nlinarith
  have hb := besselRounded_enclosure besselPrecision hp ((c.numerator : ℚ)/c.denominator)
    c.order c.terms hq hs
  rw [← integerBessel_eq besselPrecision hp c.numerator c.denominator hd] at hb
  simp only [IntegerBesselState.rational,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast,
    Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] at hb
  rw [hl,hu]
  push_cast
  constructor
  · exact hb.1
  · simpa only [add_div,mul_div_assoc] using hb.2

theorem besselRows_sound (cs : List BesselRow) (hc : cs.all BesselRow.check=true)
    (i : Fin cs.length) :
    ((cs[i]).lower : ℝ)/besselPrecision≤bessel (cs[i]).order (((cs[i]).numerator : ℝ)/(cs[i]).denominator) ∧
      bessel (cs[i]).order (((cs[i]).numerator : ℝ)/(cs[i]).denominator)≤((cs[i]).upper : ℝ)/besselPrecision :=
  (cs[i]).sound (List.all_eq_true.mp hc _ (List.getElem_mem i.isLt))

#print axioms besselRows_sound
end BecknerOnofri.HighDim.ScalarCertificate
