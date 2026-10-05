module

public import BecknerOnofri.ScalarLogBesselEndpoints
public import BecknerOnofri.CircleTailClosure

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar EntropyLogCertificate

def tailPointLower (b : MeanBracket) (z p m : CheckedLog) : ℚ :=
  (13/40)*(2*b.lower*b.mean-z.upper)+(27/40)*b.mean^2-
    ((1+b.mean)*p.upper+(1-b.mean)*m.upper)

def tailPointCheck (b : MeanBracket) (u : CheckedBessel) (z p m : CheckedLog) (L : ℚ) : Bool :=
  decide (0≤b.mean ∧ b.mean<1 ∧ u.order=0 ∧ u.argument=b.upper ∧
    0<u.value.lower ∧ z.value=u.value.upper ∧ p.value=1+b.mean ∧ m.value=1-b.mean ∧
    L≤tailPointLower b z p m)

theorem tailPoint_sound (b : MeanBracket) (u : CheckedBessel) (z p m : CheckedLog) (L : ℚ)
    (hc : tailPointCheck b u z p m L=true) : (L : ℝ)≤tailBase (b.mean : ℝ) := by
  obtain ⟨ht,ht1,hu0,harg,hpos,hz,hp,hm,hL⟩ := of_decide_eq_true hc
  have htR : (0 : ℝ)≤b.mean := by exact_mod_cast ht
  have ht1R : (b.mean : ℝ)<1 := by exact_mod_cast ht1
  have hbr := b.sound _ rfl htR ht1R
  have hparam := (parameter_mean htR ht1R).2
  have hupp := u.sound
  rw [hu0,harg] at hupp
  have hBpos : 0<bessel 0 (b.upper : ℝ) :=
    (show (0 : ℝ)<u.value.lower by exact_mod_cast hpos).trans_le hupp.1
  have hzlog := z.sound.2
  rw [hz] at hzlog
  have hzl := (Real.log_le_log hBpos hupp.2).trans hzlog
  have hzm := logBessel_mono hparam (hparam.trans hbr.2) hbr.2
  have hZ : Real.log (bessel 0 (parameter (b.mean : ℝ)))≤(z.upper : ℝ) := hzm.trans hzl
  have hplog := p.sound.2
  have hmlog := m.sound.2
  rw [hp] at hplog
  rw [hm] at hmlog
  push_cast at hplog hmlog
  have h1 := mul_le_mul_of_nonneg_left hplog (show (0 : ℝ)≤1+b.mean by linarith)
  have h2 := mul_le_mul_of_nonneg_left hmlog (show (0 : ℝ)≤1-b.mean by linarith)
  have h3 := mul_le_mul_of_nonneg_right hbr.1 (mul_nonneg (by norm_num : (0 : ℝ)≤2) htR)
  have hlow := (Rat.cast_le (K := ℝ)).mpr hL
  unfold tailPointLower at hlow
  push_cast at hlow
  unfold tailBase rate Spin.binaryCost
  nlinarith

#print axioms tailPoint_sound
end BecknerOnofri.HighDim.ScalarCertificate
