module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The common Gaussian central remainder

For s > 1 the potentially singular integrand is bounded on 0 < t < x < 1.
This proves actual Lebesgue integrability and the uniform linear remainder
bound used in the small-time Mellin decomposition. No digamma or central
integral identity is assumed here.
-/

namespace Legacy.BecknerOnofri.GaussianRemainder

open MeasureTheory Set

noncomputable def integrand (s t : ℝ) : ℝ := (1 - (1-t)^(s-1)) / t

noncomputable def remainder (s x : ℝ) : ℝ :=
  ∫ t in Ioo 0 x, integrand s t

theorem integrand_nonneg (s t : ℝ) (hs : 1 < s) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ integrand s t := by
  have hp : (1-t)^(s-1) ≤ (1 : ℝ) :=
    Real.rpow_le_one (by linarith) (by linarith) (by linarith)
  exact div_nonneg (sub_nonneg.mpr hp) ht0.le

/-- Bernoulli handles s at least 2; exponent monotonicity handles 1 < s < 2. -/
theorem integrand_le (s t : ℝ) (hs : 1 < s) (ht0 : 0 < t) (ht1 : t < 1) :
    integrand s t ≤ max (s-1) 1 := by
  unfold integrand
  by_cases hs2 : 2 ≤ s
  · have hb := one_add_mul_self_le_rpow_one_add
      (s := -t) (by linarith : (-1 : ℝ) ≤ -t) (p := s-1) (by linarith : 1 ≤ s-1)
    simp only [← sub_eq_add_neg] at hb
    apply le_trans _ (le_max_left (s-1) 1)
    apply (div_le_iff₀ ht0).2
    nlinarith
  · have hp : 1-t ≤ (1-t)^(s-1) := by
      have h := Real.rpow_le_rpow_of_exponent_ge
        (x := 1-t) (y := 1) (z := s-1)
        (by linarith : 0 < 1-t) (by linarith : 1-t ≤ 1) (by linarith : s-1 ≤ 1)
      simpa only [Real.rpow_one] using h
    apply le_trans _ (le_max_right (s-1) 1)
    apply (div_le_iff₀ ht0).2
    nlinarith

theorem integrand_continuousOn (s : ℝ) (hs : 1 < s) :
    ContinuousOn (integrand s) (Ioi 0) := by
  have hp : Continuous (fun t : ℝ => (1-t)^(s-1)) :=
    (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by linarith))
  exact (continuous_const.sub hp).continuousOn.div continuousOn_id
    (fun t ht => ne_of_gt ht)

/-- Integrability at the open endpoint follows from the uniform bound, even
though the displayed quotient has a removable singularity there. -/
theorem integrableOn_remainder (s x : ℝ) (hs : 1 < s) (hx0 : 0 < x) (hx1 : x < 1) :
    IntegrableOn (integrand s) (Ioo 0 x) := by
  have hc : IntegrableOn (fun _ : ℝ => max (s-1) 1) (Ioo 0 x) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hcont : ContinuousOn (integrand s) (Ioo 0 x) :=
    (integrand_continuousOn s hs).mono (fun _ ht => ht.1)
  apply hc.mono' (hcont.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg s t hs ht.1 (ht.2.trans hx1))]
  exact integrand_le s t hs ht.1 (ht.2.trans hx1)

theorem remainder_nonneg (s x : ℝ) (hs : 1 < s) (hx1 : x < 1) :
    0 ≤ remainder s x := by
  unfold remainder
  apply setIntegral_nonneg measurableSet_Ioo
  intro t ht
  exact integrand_nonneg s t hs ht.1 (ht.2.trans hx1)

theorem remainder_le (s x : ℝ) (hs : 1 < s) (hx0 : 0 < x) (hx1 : x < 1) :
    remainder s x ≤ max (s-1) 1 * x := by
  have hc : IntegrableOn (fun _ : ℝ => max (s-1) 1) (Ioo 0 x) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  calc
    remainder s x ≤ ∫ _t in Ioo 0 x, max (s-1) 1 :=
      setIntegral_mono_on (integrableOn_remainder s x hs hx0 hx1) hc measurableSet_Ioo
        (fun t ht => integrand_le s t hs ht.1 (ht.2.trans hx1))
    _ = max (s-1) 1 * x := by
      rw [setIntegral_const, Real.volume_real_Ioo_of_le hx0.le]
      simp only [sub_zero, smul_eq_mul, mul_comm]

/-- Bernoulli's inequality bounds the other central remainder. -/
theorem endpoint_remainder_le (s x : ℝ) (hs : 1 ≤ s) (hx : x ≤ 1) :
    (1-(1-x)^s)/s ≤ x := by
  have hb := one_add_mul_self_le_rpow_one_add
    (s := -x) (by linarith : (-1 : ℝ) ≤ -x) (p := s) hs
  simp only [← sub_eq_add_neg] at hb
  apply (div_le_iff₀ (by linarith : 0 < s)).2
  nlinarith

theorem max_shift (s : ℝ) : max (s-1) 1 + 1 = max s 2 := by
  by_cases hs : 2 ≤ s
  · rw [max_eq_left (by linarith : 1 ≤ s-1), max_eq_left hs]
    ring
  · rw [max_eq_right (by linarith : s-1 ≤ 1), max_eq_right (by linarith : s ≤ 2)]
    norm_num

/-- The actual integral remainder plus the endpoint correction is at most
max(s,2) times x, uniformly for every real s > 1 and 0 < x < 1. -/
theorem combined_remainder_le (s x : ℝ) (hs : 1 < s) (hx0 : 0 < x) (hx1 : x < 1) :
    remainder s x + (1-(1-x)^s)/s ≤ max s 2 * x := by
  calc
    remainder s x + (1-(1-x)^s)/s ≤ max (s-1) 1 * x + x :=
      add_le_add (remainder_le s x hs hx0 hx1) (endpoint_remainder_le s x hs.le hx1.le)
    _ = (max (s-1) 1 + 1) * x := by ring
    _ = max s 2 * x := by rw [max_shift]

end Legacy.BecknerOnofri.GaussianRemainder

#print axioms Legacy.BecknerOnofri.GaussianRemainder.integrableOn_remainder
#print axioms Legacy.BecknerOnofri.GaussianRemainder.combined_remainder_le
