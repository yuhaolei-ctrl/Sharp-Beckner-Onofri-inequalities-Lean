module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Actual exponential integral and rigorous bounds for the radial Poisson images. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.HighDim.RadialE1

def E1 (z : ℝ) : ℝ := ∫ t in Ioi z, Real.exp (-t)/t

theorem integrand_continuousOn {z : ℝ} (hz : 0<z) :
    ContinuousOn (fun t : ℝ=>Real.exp (-t)/t) (Ioi z) :=
  (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
    (fun t ht=>(hz.trans ht).ne')

theorem integrable {z : ℝ} (hz : 0<z) :
    IntegrableOn (fun t : ℝ=>Real.exp (-t)/t) (Ioi z) := by
  apply ((integrableOn_exp_neg_Ioi z).div_const z).mono'
    ((integrand_continuousOn hz).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (Real.exp_pos _).le (hz.trans ht).le)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hz ht.le

theorem nonneg {z : ℝ} (hz : 0<z) : 0≤E1 z :=
  setIntegral_nonneg measurableSet_Ioi (fun t ht=>div_nonneg (Real.exp_pos _).le (hz.trans ht).le)

theorem pos {z : ℝ} (hz : 0<z) : 0<E1 z := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht=>(div_pos (Real.exp_pos _) (hz.trans ht)).le)) (integrable hz)).mpr
  have he : Function.support (fun t : ℝ=>Real.exp (-t)/t) ∩ Ioi z=Ioi z := by
    apply inter_eq_right.mpr
    intro t ht
    exact (div_pos (Real.exp_pos _) (hz.trans ht)).ne'
  rw [he]
  simp

/-- The exponential-over-argument bound used for every nonzero Poisson image. -/
theorem exponential_bound {z : ℝ} (hz : 0<z) : E1 z≤Real.exp (-z)/z := by
  have h := integral_mono_ae (integrable hz) ((integrableOn_exp_neg_Ioi z).div_const z)
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht=>div_le_div_of_nonneg_left (Real.exp_pos _).le hz ht.le))
  simpa only [E1,integral_div,integral_exp_neg_Ioi] using h

theorem antitone {z w : ℝ} (hz : 0<z) (hzw : z≤w) : E1 w≤E1 z := by
  apply setIntegral_mono_set (integrable hz)
    (ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht=>(div_pos (Real.exp_pos _) (hz.trans ht)).le))
  exact Filter.Eventually.of_forall (fun t ht=>hzw.trans_lt ht)

/-- Separating the origin from any fixed positive endpoint is an exact integral identity. -/
theorem split {z w : ℝ} (hz : 0<z) (hzw : z≤w) :
    E1 z=(∫t in z..w,Real.exp (-t)/t)+E1 w := by
  have h:=intervalIntegral.integral_Ioi_sub_Ioi (integrable hz) hzw
  exact sub_eq_iff_eq_add.mp h

/-- Elementary logarithmic control, with its exact reference value E1(1).
The sharper Euler-constant identity is established separately. -/
theorem logarithmic_bound {z : ℝ} (hz : 0<z) (hz1 : z≤1) :
    E1 z≤E1 1-Real.log z := by
  rw [split hz hz1]
  have hzero (t : ℝ) (ht : t∈uIcc z 1) : t≠0 := by
    rw [uIcc_of_le hz1] at ht
    exact (hz.trans_le ht.1).ne'
  have hf : IntervalIntegrable (fun t : ℝ=>Real.exp (-t)/t) volume z 1 :=
    ((Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      hzero).intervalIntegrable
  have hg : IntervalIntegrable (fun t : ℝ=>1/t) volume z 1 :=
    (continuousOn_const.div continuousOn_id
      hzero).intervalIntegrable
  have h := intervalIntegral.integral_mono_on hz1 hf hg (fun t ht=>by
    apply div_le_div_of_nonneg_right _ (hz.trans_le ht.1).le
    exact (Real.exp_le_one_iff).mpr (by linarith [ht.1]))
  rw [integral_one_div_of_pos hz zero_lt_one] at h
  have hz0 : z≠0 := hz.ne'
  have hlog : Real.log (1/z)= -Real.log z := by rw [one_div,Real.log_inv]
  rw [hlog] at h
  linarith

#print axioms exponential_bound
#print axioms logarithmic_bound
end BecknerOnofri.HighDim.RadialE1
