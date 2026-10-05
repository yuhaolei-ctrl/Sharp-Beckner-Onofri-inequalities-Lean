module

public import Legacy.BecknerOnofri.GaussianRemainder
public import Legacy.BecknerOnofri.UniformTail
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! Exact elementary evaluation of the Gaussian central integral. -/
namespace Legacy.BecknerOnofri.GaussianCentral
open MeasureTheory Set
open GaussianRemainder

noncomputable def central (s x : ℝ) : ℝ :=
  (∫ z in Ioo 0 (1-x), z^(s-1)/(1-z)) - (1-x)^s/s

noncomputable def constant (s : ℝ) : ℝ := remainder s 1

private theorem integral_Ioo_eq_interval (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Ioo a b, f t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem integrableOn_integrand_unit (s : ℝ) (hs : 1 < s) :
    IntegrableOn (integrand s) (Ioo 0 1) := by
  have hc : IntegrableOn (fun _ : ℝ => max (s-1) 1) (Ioo 0 1) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hcont : ContinuousOn (integrand s) (Ioo 0 1) :=
    (integrand_continuousOn s hs).mono (fun _ ht => ht.1)
  apply hc.mono' (hcont.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg s t hs ht.1 ht.2)]
  exact integrand_le s t hs ht.1 ht.2

theorem intervalIntegrable_integrand_unit (s : ℝ) (hs : 1 < s) :
    IntervalIntegrable (integrand s) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).2
    (integrableOn_integrand_unit s hs)

theorem constant_eq_interval (s : ℝ) :
    constant s = ∫ t in (0:ℝ)..1, integrand s t :=
  integral_Ioo_eq_interval _ (by norm_num)

theorem constant_add_one (s : ℝ) (hs : 1 < s) :
    constant (s+1) = constant s + 1/s := by
  have hp : Continuous (fun t : ℝ => (1-t)^(s-1)) :=
    (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by linarith))
  have hi : (∫ t in (0:ℝ)..1, (1-t)^(s-1)) = 1/s := by
    rw [intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t^(s-1)) (a := (0:ℝ)) (b := 1) 1]
    norm_num only [sub_self, sub_zero]
    rw [integral_rpow (Or.inl (by linarith : -1 < s-1))]
    rw [show s-1+1=s by ring, Real.one_rpow, Real.zero_rpow (by linarith : s ≠ 0)]
    ring
  rw [constant_eq_interval, constant_eq_interval]
  calc
    (∫ t in (0:ℝ)..1, integrand (s+1) t) =
        ∫ t in (0:ℝ)..1, integrand s t + (1-t)^(s-1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      unfold integrand
      rw [show s+1-1=(s-1)+1 by ring, Real.rpow_add_one (ne_of_gt (sub_pos.mpr ht.2))]
      field_simp [ne_of_gt ht.1]
      <;> ring
    _ = (∫ t in (0:ℝ)..1, integrand s t) + (∫ t in (0:ℝ)..1, (1-t)^(s-1)) :=
      intervalIntegral.integral_add (intervalIntegrable_integrand_unit s hs) (hp.intervalIntegrable 0 1)
    _ = _ := by rw [hi]

theorem constant_two : constant 2 = 1 := by
  rw [constant_eq_interval]
  calc
    (∫ t in (0:ℝ)..1, integrand 2 t) = ∫ _t in (0:ℝ)..1, (1:ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      norm_num [integrand]
      exact ne_of_gt ht.1
    _ = 1 := by simp

private theorem integral_sqrt_reciprocal :
    (∫ z in (0:ℝ)..1, 1/(1+Real.sqrt z)) = 2-2*Real.log 2 := by
  have hg : Continuous (fun z : ℝ => 1/(1+Real.sqrt z)) :=
    continuous_const.div (continuous_const.add Real.continuous_sqrt)
      (fun z => ne_of_gt (by positivity))
  have hd : ∀ u ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun u : ℝ => u^2) (2*u) u := by
    intro u _
    convert (hasDerivAt_id u).pow 2 using 1 <;> norm_num <;> rfl
  have hchange := intervalIntegral.integral_comp_mul_deriv hd
    (show ContinuousOn (fun u : ℝ => 2*u) (uIcc 0 1) from
      (continuous_const.mul continuous_id).continuousOn) hg
  norm_num only [Function.comp_apply, zero_pow, one_pow] at hchange
  have hj : IntervalIntegrable (fun u : ℝ => 1/(1+u)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro u hu
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    change 1+u ≠ 0
    linarith [hu.1]
  have hrecip : (∫ u in (0:ℝ)..1, 1/(1+u)) = Real.log 2 := by
    rw [intervalIntegral.integral_comp_add_left (f := fun u : ℝ => 1/u) 1]
    norm_num [integral_one_div_of_pos]
  rw [← hchange]
  calc
    (∫ u in (0:ℝ)..1, 1/(1+Real.sqrt (u^2))*(2*u)) =
        ∫ u in (0:ℝ)..1, 2-2*(1/(1+u)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro u hu
      dsimp only
      rw [Real.sqrt_sq hu.1.le]
      field_simp [ne_of_gt (show 0 < 1+u by linarith [hu.1])]
      <;> ring
    _ = 2-2*Real.log 2 := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hj.const_mul 2),
        intervalIntegral.integral_const_mul, hrecip]
      norm_num

theorem constant_three_halves : constant (3/2) = 2-2*Real.log 2 := by
  rw [constant_eq_interval]
  calc
    (∫ t in (0:ℝ)..1, integrand (3/2) t) =
        ∫ t in (0:ℝ)..1, 1/(1+Real.sqrt (1-t)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have hp : (1-t)^((3:ℝ)/2-1) = Real.sqrt (1-t) := by
        rw [Real.sqrt_eq_rpow]
        norm_num
      unfold integrand
      rw [hp]
      have hs := Real.sq_sqrt (show 0 ≤ 1-t by linarith [ht.2])
      have hn : 1+Real.sqrt (1-t) ≠ 0 := ne_of_gt (by positivity)
      field_simp [ne_of_gt ht.1, hn]
      nlinarith
    _ = ∫ z in (0:ℝ)..1, 1/(1+Real.sqrt z) := by
      simpa using intervalIntegral.integral_comp_sub_left
        (f := fun z : ℝ => 1/(1+Real.sqrt z)) (a := (0:ℝ)) (b := 1) 1
    _ = _ := integral_sqrt_reciprocal

theorem central_eq (s x : ℝ) (hs : 1 < s) (hx0 : 0 < x) (hx1 : x < 1) :
    central s x = -Real.log x - (constant s + 1/s) +
      remainder s x + (1-(1-x)^s)/s := by
  have hf := intervalIntegrable_integrand_unit s hs
  have hf0 : IntervalIntegrable (integrand s) volume 0 x :=
    hf.mono_set (by simpa [uIcc_of_le hx0.le, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (Icc_subset_Icc le_rfl hx1.le : Icc (0:ℝ) x ⊆ Icc 0 1))
  have hf1 : IntervalIntegrable (integrand s) volume x 1 :=
    hf.mono_set (by simpa [uIcc_of_le hx1.le, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using
      (Icc_subset_Icc hx0.le le_rfl : Icc x 1 ⊆ Icc 0 1))
  have hi : IntervalIntegrable (fun t : ℝ => 1/t) volume x 1 :=
    (continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (hx0.trans_le (by rw [uIcc_of_le hx1.le] at ht; exact ht.1)))).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hf0 hf1
  have hlog : (∫ t in x..(1:ℝ), 1/t) = -Real.log x := by
    rw [integral_one_div_of_pos hx0 (by norm_num)]
    simp
  have hmain : (∫ z in Ioo 0 (1-x), z^(s-1)/(1-z)) =
      -Real.log x - constant s + remainder s x := by
    rw [integral_Ioo_eq_interval _ (by linarith)]
    calc
      (∫ z in (0:ℝ)..1-x, z^(s-1)/(1-z)) =
          ∫ t in x..(1:ℝ), (1-t)^(s-1)/t := by
        have hr := intervalIntegral.integral_comp_sub_left
          (f := fun t : ℝ => (1-t)^(s-1)/t) (a := (0:ℝ)) (b := 1-x) 1
        simpa only [sub_sub_cancel, sub_self, sub_zero] using hr
      _ = ∫ t in x..(1:ℝ), 1/t - integrand s t := by
        apply intervalIntegral.integral_congr
        intro t _
        unfold integrand
        ring
      _ = (∫ t in x..(1:ℝ), 1/t) - ∫ t in x..(1:ℝ), integrand s t :=
        intervalIntegral.integral_sub hi hf1
      _ = -Real.log x - constant s + remainder s x := by
        rw [hlog, constant_eq_interval]
        rw [GaussianRemainder.remainder, integral_Ioo_eq_interval _ hx0.le]
        linarith
  unfold central
  rw [hmain]
  ring

theorem central_le (s x : ℝ) (hs : 1 < s) (hx0 : 0 < x) (hx1 : x < 1) :
    central s x ≤ -Real.log x - (constant s + 1/s) + max s 2 * x := by
  rw [central_eq s x hs hx0 hx1]
  linarith [combined_remainder_le s x hs hx0 hx1]

/-- Exact evaluation of the center constants in the eight dimensions. -/
theorem constant_eq_psiCombination (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10) :
    constant ((d:ℝ)/2) + 1/((d:ℝ)/2) =
      UniformTail.psiCombination d 0 (Real.log 2) := by
  have h3 := constant_add_one 2 (by norm_num)
  have h4 := constant_add_one 3 (by norm_num)
  have h5 := constant_add_one 4 (by norm_num)
  have h52 := constant_add_one (3/2) (by norm_num)
  have h72 := constant_add_one (5/2) (by norm_num)
  have h92 := constant_add_one (7/2) (by norm_num)
  norm_num [constant_two, constant_three_halves] at h3 h4 h5 h52 h72 h92
  interval_cases d <;>
    norm_num [UniformTail.psiCombination, UniformTail.harmonicQ,
      UniformTail.oddHarmonicQ, Finset.sum_range_succ, constant_two,
      constant_three_halves] <;> linarith

/-- The exact finite combination with an arbitrary supplied Euler constant. -/
theorem constant_add_gamma_eq_psiCombination (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (gamma : ℝ) :
    constant ((d:ℝ)/2) + 1/((d:ℝ)/2) + gamma =
      UniformTail.psiCombination d gamma (Real.log 2) := by
  rw [constant_eq_psiCombination d hd3 hd10]
  unfold UniformTail.psiCombination
  split_ifs <;> ring

theorem central_le_dimension (d : ℕ) (hd3 : 3 ≤ d) (hd10 : d ≤ 10)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    central ((d:ℝ)/2) x ≤ -Real.log x -
      UniformTail.psiCombination d 0 (Real.log 2) + max ((d:ℝ)/2) 2 * x := by
  have hd : (3:ℝ) ≤ d := by exact_mod_cast hd3
  simpa only [constant_eq_psiCombination d hd3 hd10] using
    central_le ((d:ℝ)/2) x (by linarith) hx0 hx1

#print axioms constant_three_halves
#print axioms constant_eq_psiCombination
#print axioms central_eq
#print axioms central_le_dimension

end Legacy.BecknerOnofri.GaussianCentral
