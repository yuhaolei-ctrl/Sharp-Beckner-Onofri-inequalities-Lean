import BecknerOnofri.RadialThetaTail
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Exact complete heat-tail estimates in dimension twelve, including the
closed fifth-moment exponential integral used beyond time 64. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.RadialThetaTail

def heatConstant (T : ℝ) : ℝ := 2/(1-Real.exp (-3*T))

theorem heatConstant_pos {T : ℝ} (hT : 0<T) : 0<heatConstant T := by
  unfold heatConstant
  apply div_pos (by norm_num)
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

theorem theta_pos {t : ℝ} (ht : 0<t) (y : ℝ) : 0<theta t y :=
  Legacy.TorusEndpoint.TorusHeatPositivity.theta_coe_re_pos (div_pos ht Real.pi_pos) y

theorem theta_sub_one_abs_le {T t : ℝ} (hT : 0<T) (ht : T≤t) (y : ℝ) :
    |theta t y-1|≤heatConstant T*Real.exp (-t) := by
  have h := theta_truncation_error (hT.trans_le ht) le_rfl 0 y
  norm_num [partialTheta] at h
  have hden : 0<1-Real.exp (-3*T) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he : Real.exp (-3*t)≤Real.exp (-3*T) := Real.exp_le_exp.mpr (by linarith)
  have hbound : 2*Real.exp (-t)/(1-Real.exp (-3*t))≤2*Real.exp (-t)/(1-Real.exp (-3*T)) :=
    div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  have heq : -(t*3)= -3*t := by ring
  rw [heq] at h
  exact (h.trans hbound).trans_eq (by unfold heatConstant; ring)

theorem theta_le_exp {T t : ℝ} (hT : 0<T) (ht : T≤t) (y : ℝ) :
    theta t y≤1+heatConstant T*Real.exp (-t) := by
  have hh := (abs_le.mp (theta_sub_one_abs_le hT ht y)).2
  linarith

/-- Global measurability of the actual spatial Fourier-series theta. -/
theorem theta_measurable (y : ℝ) : Measurable (fun t => theta t y) := by
  unfold theta Legacy.BecknerOnofri.CircleHeat.realHeat Legacy.TorusEndpoint.TorusHeatPositivity.theta
  apply Complex.measurable_re.comp
  apply Measurable.tsum
  intro n
  fun_prop

theorem pow_twelve_sub_one_le {r : ℝ} (hr : 0≤r) :
    (1+r)^12-1≤12*r*(1+r)^11 := by
  have hs : (∑ i∈Finset.range 12,(1+r)^i)≤12*(1+r)^11 := by
    calc
      _ ≤ ∑ _∈Finset.range 12,(1+r)^11 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_right₀ (by linarith : 1≤1+r) (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by simp
  have he := geom_sum_mul (1+r) 12
  norm_num only [add_sub_cancel_left] at he
  nlinarith [mul_le_mul_of_nonneg_right hs hr]

/-- The true spatial theta power has the stated one-sided integrable majorant. -/
theorem theta_twelve_heat_tail {T t : ℝ} (hT : 0<T) (ht : T≤t) (y : ℝ) :
    (theta t y)^12-1≤
      12*heatConstant T*Real.exp (-t)*(1+heatConstant T*Real.exp (-T))^11 := by
  have hc := heatConstant_pos hT
  have hr : 0≤heatConstant T*Real.exp (-t) := by positivity
  have hpow := pow_le_pow_left₀ (theta_pos (hT.trans_le ht) y).le (theta_le_exp hT ht y) 12
  have hh := pow_twelve_sub_one_le hr
  have he : Real.exp (-t)≤Real.exp (-T) := Real.exp_le_exp.mpr (by linarith)
  have hp := pow_le_pow_left₀ (by positivity : 0≤1+heatConstant T*Real.exp (-t))
    (add_le_add_right (mul_le_mul_of_nonneg_left he hc.le) 1) 11
  have hb := mul_le_mul_of_nonneg_left hp (show 0≤12*(heatConstant T*Real.exp (-t)) by positivity)
  nlinarith

/-- Absolute domination proves integrability as well as the one-sided estimate. -/
theorem theta_twelve_heat_tail_abs {T t : ℝ} (hT : 0<T) (ht : T≤t) (y : ℝ) :
    |(theta t y)^12-1|≤
      12*heatConstant T*Real.exp (-t)*(1+heatConstant T*Real.exp (-T))^11 := by
  let B := 1+heatConstant T*Real.exp (-T)
  have hc := heatConstant_pos hT
  have hB : 1≤B := by dsimp [B]; exact le_add_of_nonneg_right (by positivity)
  have hx := (theta_pos (hT.trans_le ht) y).le
  have hupper : theta t y≤B := (theta_le_exp hT ht y).trans (by
    dsimp [B]
    gcongr)
  have hsum : (∑ i∈Finset.range 12,(theta t y)^i)≤12*B^11 := by
    calc
      _ ≤ ∑ _∈Finset.range 12,B^11 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (pow_le_pow_left₀ hx hupper i).trans
          (pow_le_pow_right₀ hB (by have := Finset.mem_range.mp hi; omega))
      _ = _ := by simp
  have hn : 0≤∑ i∈Finset.range 12,(theta t y)^i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hx i)
  calc
    _ = |(∑ i∈Finset.range 12,(theta t y)^i)*(theta t y-1)| := by
      rw [geom_sum_mul]
    _ = (∑ i∈Finset.range 12,(theta t y)^i)*|theta t y-1| := by
      rw [abs_mul,abs_of_nonneg hn]
    _ ≤ (12*B^11)*(heatConstant T*Real.exp (-t)) :=
      mul_le_mul hsum (theta_sub_one_abs_le hT ht y) (abs_nonneg _) (by positivity)
    _ = _ := by dsimp [B]; ring

def tailPolynomial (t : ℝ) : ℝ := t^5+5*t^4+20*t^3+60*t^2+120*t+120

def tailPrimitive (t : ℝ) : ℝ := -(tailPolynomial t*Real.exp (-t))

theorem tailPrimitive_hasDerivAt (t : ℝ) :
    HasDerivAt tailPrimitive (t^5*Real.exp (-t)) t := by
  have hp : HasDerivAt tailPolynomial (5*t^4+20*t^3+60*t^2+120*t+120) t := by
    convert! ((((((hasDerivAt_id t).pow 5).add (((hasDerivAt_id t).pow 4).const_mul 5)).add
      (((hasDerivAt_id t).pow 3).const_mul 20)).add (((hasDerivAt_id t).pow 2).const_mul 60)).add
      ((hasDerivAt_id t).const_mul 120)).add_const 120 using 1 <;> simp [tailPolynomial] <;> ring
  have hh := (hp.mul ((hasDerivAt_id t).neg.exp)).neg
  convert! hh using 1 <;> simp only [tailPrimitive,tailPolynomial,Pi.neg_apply,id_eq] <;> ring

theorem tailPrimitive_tendsto : Tendsto tailPrimitive atTop (𝓝 0) := by
  have hh := (((((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul 5)).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 20)).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul 60)).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 120)).add
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).const_mul 120)
  convert! hh.neg using 1
  · funext t
    simp only [tailPrimitive,tailPolynomial,pow_one,pow_zero,one_mul]
    ring
  · norm_num

theorem fifth_exp_tail_integrable {T : ℝ} (hT : 0≤T) :
    IntegrableOn (fun t : ℝ => t^5*Real.exp (-t)) (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => tailPrimitive_hasDerivAt t)
    (fun t ht => mul_nonneg (pow_nonneg (hT.trans ht.le) 5) (Real.exp_pos _).le)
    tailPrimitive_tendsto

theorem fifth_exp_tail_integral {T : ℝ} (hT : 0≤T) :
    (∫ t in Ioi T,t^5*Real.exp (-t))=Real.exp (-T)*tailPolynomial T := by
  have hh := integral_Ioi_of_hasDerivAt_of_nonneg' (fun t _ => tailPrimitive_hasDerivAt t)
    (fun t ht => mul_nonneg (pow_nonneg (hT.trans ht.le) 5) (Real.exp_pos _).le)
    tailPrimitive_tendsto
  simpa only [tailPrimitive,zero_sub,neg_neg,mul_comm] using hh

/-- Exact factorial-sum form displayed in the source. -/
theorem fifth_exp_tail_integral_factorial {T : ℝ} (hT : 0≤T) :
    (∫ t in Ioi T,t^5*Real.exp (-t))=
      Real.exp (-T)*120*∑ j∈Finset.range 6,T^j/(j.factorial : ℝ) := by
  rw [fifth_exp_tail_integral hT]
  norm_num [Finset.sum_range_succ,tailPolynomial]
  ring

/-- The complete heat integrand on the infinite tail is genuinely integrable. -/
theorem heat_tail_integrable {T : ℝ} (hT : 0<T) (y : ℝ) :
    IntegrableOn (fun t : ℝ => t^5*((theta t y)^12-1)) (Ioi T) := by
  let C := 12*heatConstant T*(1+heatConstant T*Real.exp (-T))^11
  have hc := heatConstant_pos hT
  apply ((fifth_exp_tail_integrable hT.le).const_mul C).mono'
  · exact ((measurable_id.pow_const 5).mul
      (((theta_measurable y).pow_const 12).sub measurable_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (hT.le.trans ht.le) 5)]
    have hh := mul_le_mul_of_nonneg_left (theta_twelve_heat_tail_abs hT ht.le y)
      (pow_nonneg (hT.le.trans ht.le) 5)
    convert! hh using 1 <;> dsimp [C] <;> ring

/-- Source's complete bound beyond T, including the Gamma(6) normalization. -/
theorem heat_tail_integral_le {T : ℝ} (hT : 0<T) (y : ℝ) :
    (1/120:ℝ)*(∫ t in Ioi T,t^5*((theta t y)^12-1))≤
      (12*heatConstant T*(1+heatConstant T*Real.exp (-T))^11/120)*
        Real.exp (-T)*120*∑ j∈Finset.range 6,T^j/(j.factorial : ℝ) := by
  let C := 12*heatConstant T*(1+heatConstant T*Real.exp (-T))^11
  have hh : (∫ t in Ioi T,t^5*((theta t y)^12-1))≤
      ∫ t in Ioi T,C*(t^5*Real.exp (-t)) := by
    apply integral_mono_ae (heat_tail_integrable hT y)
      ((fifth_exp_tail_integrable hT.le).const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hh := mul_le_mul_of_nonneg_left (theta_twelve_heat_tail hT ht.le y)
      (pow_nonneg (hT.le.trans ht.le) 5)
    convert! hh using 1 <;> dsimp [C] <;> ring
  rw [integral_const_mul,fifth_exp_tail_integral_factorial hT.le] at hh
  have hb := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/120)
  convert! hb using 1 <;> dsimp [C] <;> ring

#print axioms heat_tail_integrable
#print axioms heat_tail_integral_le
#print axioms theta_twelve_heat_tail
#print axioms fifth_exp_tail_integral_factorial
end BecknerOnofri.HighDim.RadialThetaTail
