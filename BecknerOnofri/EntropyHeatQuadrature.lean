module

public import BecknerOnofri.EntropyTailCore
public import BecknerOnofri.RadialQuadrature

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.BecknerOnofri.ThetaDomination

theorem heatComplement_continuousOn {a : ℝ} (ha : 0 < a) :
    ContinuousOn heatComplement (Ici a) := by
  have hc : ContinuousOn realTheta (Ici a) := by
    apply continuousOn_tsum (fun j : ℤ => ?_) (summable_realTheta ha)
    · intro j s hs
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hs) (sq_nonneg (j : ℝ))
    · fun_prop
  change ContinuousOn (fun s => (realTheta s)^12-(1+2*Real.exp (-s))^12) (Ici a)
  exact (hc.pow 12).sub (by fun_prop)

theorem shifted_fifth_integral (a b η : ℝ) :
    (∫ s in a..b, (s-η)^5) = ((b-η)^6-(a-η)^6)/6 := by
  have hd (s : ℝ) : HasDerivAt (fun x : ℝ => (x-η)^6/6) ((s-η)^5) s := by
    convert! (((hasDerivAt_id s).sub_const η).pow 6).div_const 6 using 1 <;> simp only [id_eq] <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((continuous_id.sub continuous_const).pow 5 |>.intervalIntegrable a b)
  convert! h using 1 <;> ring

theorem positive_fifth_integral_above {a b η : ℝ} (hab : a ≤ b) (hη : η ≤ a) :
    (∫ s in a..b, (max (s-η) 0)^5) = ((b-η)^6-(a-η)^6)/6 := by
  rw [← shifted_fifth_integral]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hab] at hs
  dsimp only
  rw [max_eq_left (by linarith [hs.1])]

theorem positive_fifth_integral_below {a b η : ℝ} (hab : a ≤ b) (hη : b ≤ η) :
    (∫ s in a..b, (max (s-η) 0)^5) = 0 := by
  calc
    _ = ∫ _s in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hab] at hs
      dsimp only
      rw [max_eq_right (by linarith [hs.2]), zero_pow (by norm_num : 5 ≠ 0)]
    _ = 0 := by simp

theorem positive_fifth_integral {a b η : ℝ} (hab : a ≤ b) :
    (∫ s in a..b, (max (s-η) 0)^5) =
      ((max (b-η) 0)^6-(max (a-η) 0)^6)/6 := by
  by_cases hb : b ≤ η
  · rw [positive_fifth_integral_below hab hb,
      max_eq_right (by linarith : b-η ≤ 0), max_eq_right (by linarith : a-η ≤ 0)]
    norm_num
  · by_cases ha : η ≤ a
    · rw [positive_fifth_integral_above hab ha,
        max_eq_left (by linarith : 0 ≤ b-η), max_eq_left (by linarith : 0 ≤ a-η)]
    · have hi (v w : ℝ) : IntervalIntegrable (fun s : ℝ => (max (s-η) 0)^5) volume v w :=
        (((continuous_id.sub continuous_const).max continuous_const).pow 5).intervalIntegrable v w
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi a η) (hi η b),
        positive_fifth_integral_below (le_of_not_ge ha) le_rfl,
        positive_fifth_integral_above (le_of_not_ge hb) le_rfl,
        max_eq_left (by linarith : 0 ≤ b-η), max_eq_right (by linarith : a-η ≤ 0)]
      norm_num

theorem heat_panel_integrable {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (η : ℝ) :
    IntervalIntegrable (fun s : ℝ => (max (s-η) 0)^5*heatComplement s) volume v w := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hvw]
  exact (((continuous_id.sub continuous_const).max continuous_const).pow 5).continuousOn.mul
    ((heatComplement_continuousOn hv).mono (fun _ hs => hs.1))

/-- The exact shifted panel rule, including panels below or crossing η. -/
theorem heat_panel_bound {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) (η : ℝ) :
    (1/120 : ℝ)*(∫ s in v..w, (max (s-η) 0)^5*heatComplement s) ≤
      (heatComplement v/720)*((max (w-η) 0)^6-(max (v-η) 0)^6) := by
  have h := RadialQuadrature.weighted_interval_upper hvw
    (fun s : ℝ => (max (s-η) 0)^5) heatComplement
    ((((continuous_id.sub continuous_const).max continuous_const).pow 5).intervalIntegrable v w)
    (heat_panel_integrable hv hvw η)
    (fun s _ => pow_nonneg (le_max_right _ _) 5)
    (fun s hs => heatComplement_antitone hv (hv.trans_le hs.1) hs.1)
  rw [positive_fifth_integral hvw] at h
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/120)
  convert! hm using 1 <;> ring

#print axioms heat_panel_bound
end BecknerOnofri.HighDim.EntropyTail
