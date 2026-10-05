import Legacy.BecknerOnofri.GaussianCentral

/-! The nonlinear substitution identifying the central heat contribution. -/
namespace Legacy.BecknerOnofri.GaussianCentral
open MeasureTheory Set

private theorem integral_Ioo_eq_interval (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Ioo a b, f t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

private theorem change_integrand (s a t : ℝ) (ha : 0 < a) (hat : a < t) :
    (t-a)^(s-1)*(Real.pi/t)^s =
      Real.pi^s * ((1-a/t)^(s-1)/(1-(1-a/t))) * (a/t^2) := by
  have ht : 0 < t := ha.trans hat
  have ht' : t ≠ 0 := ne_of_gt ht
  have hs' : t^s ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht s)
  rw [Real.div_rpow Real.pi_nonneg ht.le]
  rw [show 1-a/t=(t-a)/t by field_simp]
  rw [Real.div_rpow (sub_nonneg.mpr hat.le) ht.le, Real.rpow_sub_one ht' s]
  field_simp [ht', hs', ne_of_gt ha]
  <;> ring

/-- The central heat term is exactly the elementary center after z = 1-a/t. -/
theorem rawCentral_eq (s a : ℝ) (hs : 1 < s) (ha : 0 < a) (hapi : a < Real.pi) :
    (∫ t in Ioo a Real.pi, (t-a)^(s-1)*((Real.pi/t)^s-1)) =
      Real.pi^s * central s (a/Real.pi) := by
  have ha' := ne_of_gt ha
  have hp' := ne_of_gt Real.pi_pos
  have hden (t : ℝ) (ht : t ∈ uIcc a Real.pi) : t ≠ 0 := by
    rw [uIcc_of_le hapi.le] at ht
    exact ne_of_gt (ha.trans_le ht.1)
  have hd : ∀ t ∈ uIcc a Real.pi,
      HasDerivAt (fun t : ℝ => 1-a/t) (a/t^2) t := by
    intro t ht
    convert (hasDerivAt_const t 1).fun_sub
      ((hasDerivAt_const t a).fun_div (hasDerivAt_id t) (hden t ht)) using 1 <;>
      norm_num <;> first | rfl | ring
  have hdc : ContinuousOn (fun t : ℝ => a/t^2) (uIcc a Real.pi) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero _ (hden t ht))
  have hgc : ContinuousOn (fun z : ℝ => z^(s-1)/(1-z))
      ((fun t : ℝ => 1-a/t) '' uIcc a Real.pi) := by
    apply (continuousOn_id.rpow_const (fun _ _ => Or.inr (by linarith))).div
      (continuousOn_const.sub continuousOn_id)
    rintro z ⟨t, ht, rfl⟩
    change 1-(1-a/t) ≠ 0
    simp only [sub_sub_cancel]
    exact div_ne_zero ha' (hden t ht)
  have hchange := intervalIntegral.integral_comp_mul_deriv' hd hdc hgc
  simp only [Function.comp_apply, div_self ha', sub_self] at hchange
  have hp : Continuous (fun t : ℝ => (t-a)^(s-1)) :=
    (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by linarith))
  have hi0 : IntervalIntegrable (fun t : ℝ => (t-a)^(s-1)) volume a Real.pi :=
    hp.intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun t : ℝ => (t-a)^(s-1)*(Real.pi/t)^s)
      volume a Real.pi := by
    apply ContinuousOn.intervalIntegrable
    exact hp.continuousOn.mul
      ((continuousOn_const.div continuousOn_id hden).rpow_const
        (fun _ _ => Or.inr (by linarith)))
  have hmain : (∫ t in a..Real.pi, (t-a)^(s-1)*(Real.pi/t)^s) =
      Real.pi^s * ∫ z in (0:ℝ)..(1-a/Real.pi), z^(s-1)/(1-z) := by
    calc
      _ = ∫ t in a..Real.pi,
          Real.pi^s * (((1-a/t)^(s-1)/(1-(1-a/t)))*(a/t^2)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hapi.le
        intro t ht
        dsimp only
        rw [change_integrand s a t ha ht.1]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, hchange]
  have hpower : (∫ t in a..Real.pi, (t-a)^(s-1)) = (Real.pi-a)^s/s := by
    rw [intervalIntegral.integral_comp_sub_right (f := fun t : ℝ => t^(s-1)) a]
    rw [sub_self, integral_rpow (Or.inl (by linarith : -1 < s-1))]
    rw [show s-1+1=s by ring, Real.zero_rpow (by linarith : s ≠ 0), sub_zero]
  have hpow : (Real.pi-a)^s = Real.pi^s*(1-a/Real.pi)^s := by
    rw [show Real.pi-a=Real.pi*(1-a/Real.pi) by field_simp]
    rw [Real.mul_rpow Real.pi_nonneg (by have := (div_lt_one Real.pi_pos).2 hapi; linarith)]
  have hx : 0 ≤ 1-a/Real.pi := by
    have := (div_lt_one Real.pi_pos).2 hapi
    linarith
  rw [integral_Ioo_eq_interval _ hapi.le]
  calc
    _ = (∫ t in a..Real.pi, (t-a)^(s-1)*(Real.pi/t)^s) -
        ∫ t in a..Real.pi, (t-a)^(s-1) := by
      rw [← intervalIntegral.integral_sub hi1 hi0]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by
      rw [hmain, hpower, hpow, central, integral_Ioo_eq_interval _ hx]
      ring

#print axioms rawCentral_eq
end Legacy.BecknerOnofri.GaussianCentral
