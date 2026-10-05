module

public import BecknerOnofri.EntropyHeatRationalEnclosure
public import BecknerOnofri.EntropyCertifiedExp

@[expose] public section

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open ExpCertificate

structure SmallEndpoint where
  point : ℚ
  upper : ℚ
  directExp : Entry
  modularExp : Entry

def SmallEndpoint.check (p : SmallEndpoint) : Bool := decide (
  0 < p.point ∧ 0 ≤ p.directExp.lowerBound ∧ p.modularExp.upperBound < 1 ∧
  p.directExp.argument = p.point ∧
  p.modularExp.argument ≤ piLower^2/p.point ∧
  smallUpper p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper)

theorem SmallEndpoint.sound (p : SmallEndpoint) (hc : p.check = true)
    (hd : p.directExp.Valid) (hm : p.modularExp.Valid) :
    heatComplement (p.point : ℝ) ≤ (p.upper : ℝ) := by
  have h : 0 < p.point ∧ 0 ≤ p.directExp.lowerBound ∧ p.modularExp.upperBound < 1 ∧
      p.directExp.argument = p.point ∧ p.modularExp.argument ≤ piLower^2/p.point ∧
      smallUpper p.point p.directExp.lowerBound p.modularExp.upperBound ≤ p.upper :=
    of_decide_eq_true hc
  apply smallUpper_sound p.point p.directExp.lowerBound p.modularExp.argument
    p.modularExp.upperBound p.upper h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  · simpa only [← h.2.2.2.1] using hd.1
  · exact hm.2

structure LargeEndpoint where
  point : ℚ
  upper : ℚ
  e1 : Entry
  e4 : Entry
  e9 : Entry
  e16 : Entry
  e25 : Entry
  e11 : Entry

def LargeEndpoint.check (p : LargeEndpoint) : Bool := decide (
  0 < p.point ∧ p.e11.upperBound < 1 ∧
  p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
  p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
  p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
  directUpper p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
    p.e25.upperBound p.e11.upperBound ≤ p.upper)

theorem LargeEndpoint.sound (p : LargeEndpoint) (hc : p.check = true)
    (h1 : p.e1.Valid) (h4 : p.e4.Valid) (h9 : p.e9.Valid)
    (h16 : p.e16.Valid) (h25 : p.e25.Valid) (h11 : p.e11.Valid) :
    heatComplement (p.point : ℝ) ≤ (p.upper : ℝ) := by
  have h : 0 < p.point ∧ p.e11.upperBound < 1 ∧
      p.e1.argument = p.point ∧ p.e4.argument = 4*p.point ∧
      p.e9.argument = 9*p.point ∧ p.e16.argument = 16*p.point ∧
      p.e25.argument = 25*p.point ∧ p.e11.argument = 11*p.point ∧
      directUpper p.e1.upperBound p.e4.upperBound p.e9.upperBound p.e16.upperBound
        p.e25.upperBound p.e11.upperBound ≤ p.upper := of_decide_eq_true hc
  obtain ⟨hs, hlt, he1, he4, he9, he16, he25, he11, hU⟩ := h
  apply directUpper_sound p.point p.e1.upperBound p.e4.upperBound p.e9.upperBound
    p.e16.upperBound p.e25.upperBound p.e11.upperBound p.upper hs hlt hU
  · simpa only [Entry.Valid, he1] using h1.2
  · simpa only [he4, Rat.cast_mul, Rat.cast_ofNat, neg_mul] using h4.2
  · simpa only [he9, Rat.cast_mul, Rat.cast_ofNat, neg_mul] using h9.2
  · simpa only [he16, Rat.cast_mul, Rat.cast_ofNat, neg_mul] using h16.2
  · simpa only [he25, Rat.cast_mul, Rat.cast_ofNat, neg_mul] using h25.2
  · simpa only [he11, Rat.cast_mul, Rat.cast_ofNat, neg_mul] using h11.2

#print axioms SmallEndpoint.sound
#print axioms LargeEndpoint.sound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
