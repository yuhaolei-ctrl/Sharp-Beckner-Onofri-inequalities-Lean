module

public import BecknerOnofri.RadialE1
public import BecknerOnofri.EulerConstantBound
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

@[expose] public section

/-! The exponential-integral logarithmic singularity with its actual
Euler--Mascheroni constant, derived from the differentiated Gamma integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.HighDim.RadialE1

/-- The genuine derivative-of-Gamma integral at one. -/
theorem integral_log_exp :
    (∫ t : ℝ in Ioi 0, Real.log t*Real.exp (-t))= -Real.eulerMascheroniConstant := by
  have h := Complex.hasDerivAt_GammaIntegral (s:=1) (by norm_num)
  have he : Complex.GammaIntegral =ᶠ[𝓝 (1:ℂ)] Complex.Gamma := by
    have hopen : IsOpen {s : ℂ | 0<s.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds (by norm_num : (1:ℂ)∈{s : ℂ | 0<s.re})] with s hs
    exact (Complex.Gamma_eq_integral hs).symm
  have hval := (h.congr_of_eventuallyEq he.symm).unique Complex.hasDerivAt_Gamma_one
  simp only [sub_self,Complex.cpow_zero,one_mul] at hval
  have hval' := congrArg Complex.re hval
  simpa only [← Complex.ofReal_mul,integral_complex_ofReal,Complex.ofReal_re,Complex.neg_re] using hval'

theorem log_exp_integrable :
    IntegrableOn (fun t : ℝ => Real.log t*Real.exp (-t)) (Ioi 0) := by
  by_contra h
  have hzero := integral_undef h
  rw [integral_log_exp] at hzero
  have hp := Real.one_half_lt_eulerMascheroniConstant
  linarith

theorem log_exp_tendsto : Tendsto (fun t : ℝ => Real.log t*Real.exp (-t)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    exact mul_nonneg (Real.log_nonneg ht) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    rw [pow_one]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)

def logTailPrimitive (t : ℝ) : ℝ := -(Real.log t*Real.exp (-t))

theorem logTailPrimitive_hasDerivAt {t : ℝ} (ht : 0<t) :
    HasDerivAt logTailPrimitive (Real.log t*Real.exp (-t)-Real.exp (-t)/t) t := by
  have h := ((Real.hasDerivAt_log ht.ne').mul ((hasDerivAt_id t).neg.exp)).neg
  convert! h using 1 <;> simp only [logTailPrimitive,Pi.neg_apply,id_eq] <;> ring

theorem logarithmic_tail_identity {z : ℝ} (hz : 0<z) :
    (∫ t in Ioi z,Real.log t*Real.exp (-t))=Real.exp (-z)*Real.log z+E1 z := by
  have hi : IntegrableOn (fun t : ℝ => Real.log t*Real.exp (-t)) (Ioi z) :=
    log_exp_integrable.mono_set (Ioi_subset_Ioi hz.le)
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => logTailPrimitive_hasDerivAt (hz.trans_le ht)) (hi.sub (integrable hz)) log_exp_tendsto.neg
  rw [integral_sub hi (integrable hz)] at hh
  simp only [neg_zero] at hh
  change _-E1 z=0-logTailPrimitive z at hh
  dsimp [logTailPrimitive] at hh
  linarith

/-- Source's sharp logarithmic bound for the actual improper integral E1. -/
theorem euler_logarithmic_bound {z : ℝ} (hz : 0<z) :
    E1 z≤ -Real.eulerMascheroniConstant-Real.log z+z := by
  have hlogint : IntervalIntegrable Real.log volume 0 z := intervalIntegral.intervalIntegrable_log'
  have hexpint : IntervalIntegrable (fun t : ℝ => Real.exp (-t)) volume 0 z :=
    (Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 z
  have hprodint : IntervalIntegrable (fun t : ℝ => Real.log t*Real.exp (-t)) volume 0 z :=
    intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le |>.mpr
      (log_exp_integrable.mono_set Ioc_subset_Ioi_self)
  have hf : IntervalIntegrable (fun t : ℝ => (Real.log z-Real.log t)*Real.exp (-t)) volume 0 z := by
    simpa only [sub_mul] using (hexpint.const_mul (Real.log z)).sub hprodint
  have hg : IntervalIntegrable (fun t : ℝ => Real.log z-Real.log t) volume 0 z :=
    intervalIntegrable_const.sub hlogint
  have hbound : (∫ t in 0..z,(Real.log z-Real.log t)*Real.exp (-t))≤
      ∫ t in 0..z,Real.log z-Real.log t := by
    simp only [intervalIntegral.integral_of_le hz.le]
    apply setIntegral_mono_on hf.1 hg.1 measurableSet_Ioc
    intro t ht
    have ht0 := ht.1
    have hl : 0≤Real.log z-Real.log t := sub_nonneg.mpr (Real.log_le_log ht0 ht.2)
    exact mul_le_of_le_one_right hl (Real.exp_le_one_iff.mpr (by linarith))
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi log_exp_integrable hz.le
  rw [integral_log_exp,logarithmic_tail_identity hz] at hsplit
  have heint : (∫ t in 0..z,Real.exp (-t))=1-Real.exp (-z) := by
    have hh := intervalIntegral.integral_Ioi_sub_Ioi (integrableOn_exp_neg_Ioi 0) hz.le
    simpa only [integral_exp_neg_Ioi,neg_zero,Real.exp_zero] using hh.symm
  simp_rw [sub_mul] at hbound
  rw [intervalIntegral.integral_sub (hexpint.const_mul _) hprodint,
    intervalIntegral.integral_const_mul,heint,
    intervalIntegral.integral_sub intervalIntegrable_const hlogint,
    intervalIntegral.integral_const,integral_log_from_zero] at hbound
  simp only [sub_zero,smul_eq_mul] at hbound
  nlinarith

theorem rational_logarithmic_bound {z : ℝ} (hz : 0<z) :
    E1 z≤ -(5771/10000:ℝ)-Real.log z+z := by
  have h := euler_logarithmic_bound hz
  have hc := EulerConstantBound.euler_lower
  linarith

#print axioms integral_log_exp
#print axioms euler_logarithmic_bound
end BecknerOnofri.HighDim.RadialE1
