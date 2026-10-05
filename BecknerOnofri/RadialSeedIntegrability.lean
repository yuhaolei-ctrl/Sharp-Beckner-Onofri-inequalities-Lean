import BecknerOnofri.RadialSeedProfile

/-! Actual radial integrability from the proved logarithmic origin estimate
and exact endpoint substitution, before any numerical certificate is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialSeedReduction
open RadialGreenHeat RadialQuadrature

def profileIntegrand (S : ℝ) : ℝ := radialWeight S*Real.exp ((7/10:ℝ)*radialGreen 12 S)

theorem profileIntegrand_measurable : Measurable profileIntegrand := by
  unfold profileIntegrand radialWeight
  exact ((measurable_id.pow_const 5).div (Real.continuous_sqrt.measurable.comp
    (measurable_const.sub measurable_id))).mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul (radialGreen_measurable 12)))

theorem profileIntegrand_nonneg {S : ℝ} (hS : 0≤S) : 0≤profileIntegrand S :=
  mul_nonneg (radialWeight_nonneg hS) (Real.exp_pos _).le

theorem origin_integrable (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) (ha0 : a 0=1) :
    IntervalIntegrable profileIntegrand volume 0 sourceS₀ := by
  let p : ℝ := 5-(7/10:ℝ)*sourceC
  have hp : -1<p := by dsimp [p]; linarith [source_power_pos]
  have hpow : IntervalIntegrable (fun S : ℝ => S^p) volume 0 sourceS₀ :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hi := ((hpow.const_mul (Real.exp ((7/10:ℝ)*originConstant a n))).div_const
    (Real.sqrt (1-sourceS₀))).1
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le sourceS₀_pos.le).mpr
  refine hi.mono' profileIntegrand_measurable.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with S hS
  rw [Real.norm_eq_abs,abs_of_nonneg (profileIntegrand_nonneg hS.1.le)]
  have hd0 : 0 < Real.sqrt (1-sourceS₀) := Real.sqrt_pos.mpr (sub_pos.mpr (sourceS₀_lt.trans (by norm_num)))
  have hdS : 0 < Real.sqrt (1-S) := Real.sqrt_pos.mpr (sub_pos.mpr (hS.2.trans_lt (sourceS₀_lt.trans (by norm_num))))
  have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (profile_origin_bound a n ha ha0 hS) (by norm_num : (0:ℝ)≤7/10))
  change (S^5/Real.sqrt (1-S))*Real.exp ((7/10:ℝ)*radialGreen 12 S) ≤ _
  rw [div_mul_eq_mul_div]
  calc
    _ ≤ (S^5*Real.exp ((7/10:ℝ)*(originConstant a n-sourceC*Real.log S)))/Real.sqrt (1-S) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hex (pow_nonneg hS.1.le 5)) hdS.le
    _ = Real.exp ((7/10:ℝ)*originConstant a n)*S^p/Real.sqrt (1-S) := by
      rw [RadialOrigin.logarithmic_exponential_identity hS.1]
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hS.1.le _)) hd0
      (Real.sqrt_le_sqrt (by linarith [hS.2]))

theorem interior_integrable {a b : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<1) :
    IntervalIntegrable profileIntegrand volume a b := by
  have hw : IntervalIntegrable radialWeight volume a b :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hab] using radialWeight_continuousOn hab hb)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  apply (hw.mul_const (Real.exp ((7/10:ℝ)*radialGreen 12 a))).1.mono'
    profileIntegrand_measurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with S hS
  have hS0 : 0<S := ha.trans hS.1
  rw [Real.norm_eq_abs,abs_of_nonneg (profileIntegrand_nonneg hS0.le)]
  apply mul_le_mul_of_nonneg_left _ (radialWeight_nonneg hS0.le)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left ((radialGreen_antitone (by norm_num : 0<12))
    ⟨ha,by norm_num; linarith⟩ ⟨hS0,by norm_num; linarith [hS.2]⟩ hS.1.le) (by norm_num)

/-- Integrability of the entire exact radial integrand is unconditional. -/
theorem profile_integrable : IntervalIntegrable profileIntegrand volume 0 1 := by
  have h0 := origin_integrable (fun _ => 1) 0 (by intro i j h; rfl) rfl
  have hm := interior_integrable sourceS₀_pos sourceS₀_lt.le (by norm_num : (7/16:ℝ)<1)
  have he := endpoint_radial_integrable (radialGreen 12) (radialGreen_measurable 12)
    (radialGreen_antitone (by norm_num))
  exact (h0.trans hm).trans he

#print axioms origin_integrable
#print axioms profile_integrable
end BecknerOnofri.HighDim.RadialSeedReduction
