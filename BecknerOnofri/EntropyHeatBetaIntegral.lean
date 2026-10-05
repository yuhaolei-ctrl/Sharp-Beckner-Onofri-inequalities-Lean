import BecknerOnofri.RadialHeatTail

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.HighDim.EntropyTail

def betaPrimitive (η s : ℝ) : ℝ := (1-η/s)^5/(5*η)

theorem betaPrimitive_hasDerivAt {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    HasDerivAt (betaPrimitive η) ((s-η)^4/s^6) s := by
  have h := (((hasDerivAt_const s (1 : ℝ)).sub
    ((hasDerivAt_const s η).div (hasDerivAt_id s) hs.ne')).pow 5).div_const (5*η)
  convert! h using 1
  dsimp only [id_eq, Pi.sub_apply, Pi.div_apply]
  norm_num only [Nat.cast_ofNat, show 5-1=4 by omega, zero_mul, mul_one, zero_sub, neg_neg]
  field_simp
  <;> ring

theorem betaPrimitive_tendsto (η : ℝ) :
    Tendsto (betaPrimitive η) atTop (𝓝 (1/(5*η))) := by
  have h : Tendsto (fun s : ℝ => η/s) atTop (𝓝 0) := tendsto_id.const_div_atTop η
  have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub h).pow 5).div_const (5*η)
  convert! hh using 1 <;> simp only [sub_zero, one_pow, betaPrimitive]

theorem beta_integrable {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun s : ℝ => (s-η)^4/s^6) (Ioi η) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun s hs => betaPrimitive_hasDerivAt hη (hη.trans_le hs))
    (fun s hs => div_nonneg (by positivity) (pow_nonneg (hη.trans hs).le _))
    (betaPrimitive_tendsto η)

theorem beta_integral {η : ℝ} (hη : 0 < η) :
    (∫ s in Ioi η, (s-η)^4/s^6) = 1/(5*η) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun s hs => betaPrimitive_hasDerivAt hη (hη.trans_le hs))
    (fun s hs => div_nonneg (by positivity : (0 : ℝ) ≤ (s-η)^4)
      (pow_nonneg (hη.trans hs).le 6)) (betaPrimitive_tendsto η)
  simpa only [betaPrimitive, div_self hη.ne', sub_self, zero_pow (by norm_num : 5 ≠ 0),
    zero_div, sub_zero] using h

#print axioms beta_integral
end BecknerOnofri.HighDim.EntropyTail
