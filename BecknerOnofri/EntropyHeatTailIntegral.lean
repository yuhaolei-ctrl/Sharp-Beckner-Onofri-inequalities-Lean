import BecknerOnofri.EntropyTailCore
import BecknerOnofri.RadialHeatTail

noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropyTail

theorem scaled_fifth_integral {T : ℝ} (hT : 0 ≤ T) :
    (∫ s in Ioi T, s^5*Real.exp (-4*s)) =
      Real.exp (-4*T)*RadialThetaTail.tailPolynomial (4*T)/4^6 := by
  calc
    _ = (1/(4 : ℝ)^5)*(∫ s in Ioi T, (4*s)^5*Real.exp (-(4*s))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with s
      rw [show -(4*s) = -4*s by ring]
      ring
    _ = (1/(4 : ℝ)^5)*(4⁻¹*(∫ s in Ioi (4*T), s^5*Real.exp (-s))) := by
      rw [integral_comp_mul_left_Ioi (fun s : ℝ => s^5*Real.exp (-s)) T (by norm_num : (0 : ℝ) < 4)]
      rfl
    _ = _ := by
      rw [RadialThetaTail.fifth_exp_tail_integral (by positivity)]
      ring

theorem scaled_fifth_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun s : ℝ => s^5*Real.exp (-4*s)) (Ioi T) := by
  apply Integrable.of_integral_ne_zero
  rw [scaled_fifth_integral hT]
  apply ne_of_gt
  apply div_pos
  · apply mul_pos (Real.exp_pos _)
    unfold RadialThetaTail.tailPolynomial
    positivity
  · norm_num

theorem exponential_eighty_upper : Real.exp (-80) ≤ (25000/67957 : ℝ)^80 := by
  have he : (67957/25000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h := one_div_le_one_div_of_le (show (0 : ℝ) < (67957/25000)^80 by positivity)
    (pow_le_pow_left₀ (by positivity) he 80)
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one, one_div, ← Real.exp_neg] at h
  convert! h using 1 <;> norm_num [inv_pow]

theorem far_integral_rational_bound :
    (26/120 : ℝ)*(∫ s in Ioi (20 : ℝ), s^5*Real.exp (-4*s)) <
      667/(2*10^32) := by
  rw [scaled_fifth_integral (by norm_num)]
  norm_num only [RadialThetaTail.tailPolynomial]
  have h := exponential_eighty_upper
  have hp := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤
    (26/120)*RadialThetaTail.tailPolynomial 80/4^6 by norm_num [RadialThetaTail.tailPolynomial])
  have hnum : ((26/120 : ℝ)*RadialThetaTail.tailPolynomial 80/4^6)*(25000/67957)^80 <
      667/(2*10^32) := by norm_num [RadialThetaTail.tailPolynomial]
  norm_num only [RadialThetaTail.tailPolynomial] at hp hnum
  nlinarith

/-- Actual omitted Mellin integral, including the endpoint and numerical constant. -/
theorem heat_integral_beyond_twenty {η : ℝ} (hη : 0 < η) (hη20 : η ≤ 20) :
    (1/120 : ℝ)*(∫ s in Ioi (20 : ℝ), (s-η)^5*heatComplement s) < 667/(2*10^32) := by
  have hi : IntegrableOn (fun s : ℝ => (s-η)^5*heatComplement s) (Ioi (20 : ℝ)) :=
    (heat_integrable hη).mono_set (fun _ hs => hη20.trans_lt hs)
  have hg := (scaled_fifth_integrable (T := 20) (by norm_num)).const_mul 26
  have h := setIntegral_mono_on hi hg measurableSet_Ioi (fun s hs => ?_)
  · have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/120)
    rw [integral_const_mul] at hm
    apply lt_of_le_of_lt _ far_integral_rational_bound
    convert! hm using 1 <;> ring
  · have hs' : (20 : ℝ) < s := hs
    have hb := (heatComplement_far_upper hs.le).le
    have hp : (s-η)^5 ≤ s^5 := pow_le_pow_left₀ (by linarith : 0 ≤ s-η) (by linarith) 5
    have hh := mul_le_mul hp hb (heatComplement_nonneg (by linarith)) (by positivity : (0 : ℝ) ≤ s^5)
    convert! hh using 1 <;> ring

#print axioms heat_integral_beyond_twenty
end BecknerOnofri.HighDim.EntropyTail
