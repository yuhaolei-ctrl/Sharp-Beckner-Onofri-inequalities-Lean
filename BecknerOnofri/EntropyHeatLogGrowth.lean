module

public import BecknerOnofri.EntropyHeatSlopeMellin
public import BecknerOnofri.EntropyHeatBetaIntegral
public import BecknerOnofri.EntropyHeatGlobal
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Topology
namespace BecknerOnofri.HighDim.EntropyTail

theorem gaussianSlope_upper {η : ℝ} (hη : 0 < η) :
    gaussianSlope η ≤ Real.pi^6/(120*η) := by
  rw [gaussianSlope_eq_heatIntegral hη]
  have hi := slope_heat_integrable hη
  have hg := (beta_integrable hη).const_mul (Real.pi^6)
  have hm := setIntegral_mono_on hi hg measurableSet_Ioi (fun s hs => ?_)
  · rw [integral_const_mul, beta_integral hη] at hm
    have hh := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1/24)
    convert! hh using 1 <;> field_simp <;> ring
  · have hs' : 0 < s := hη.trans hs
    have hb := heatComplement_global_upper hs'
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ (s-η)^4)
    convert! hh using 1 <;> ring

theorem heatIntegral_hasDerivAt {η : ℝ} (hη : 0 < η) :
    HasDerivAt heatIntegral (-gaussianSlope η) η := by
  apply (gaussianTail_hasDerivAt hη).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hη] with t ht
  exact heatIntegral_eq_gaussianTail ht

theorem gaussianTail_log_corrected_hasDerivAt {η : ℝ} (hη : 0 < η) :
    HasDerivAt (fun t => gaussianTail t+(Real.pi^6/120)*Real.log t)
      (-gaussianSlope η+(Real.pi^6/120)/η) η := by
  have h := (gaussianTail_hasDerivAt hη).add
    ((Real.hasDerivAt_log hη.ne').const_mul (Real.pi^6/120))
  convert! h using 1 <;> simp only [div_eq_mul_inv]

theorem gaussianTail_log_corrected_monotone :
    MonotoneOn (fun t => gaussianTail t+(Real.pi^6/120)*Real.log t) (Ioi (0 : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (gaussianTail_log_corrected_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [isOpen_Ioi.interior_eq] at ht
    exact (gaussianTail_log_corrected_hasDerivAt ht).hasDerivWithinAt
  · intro t ht
    rw [isOpen_Ioi.interior_eq] at ht
    have h := gaussianSlope_upper ht
    have he : Real.pi^6/(120*t) = (Real.pi^6/120)/t := by ring
    rw [he] at h
    linarith

/-- The logarithmic growth estimate used for the unbounded scalar-index range. -/
theorem heatIntegral_log_growth {η ξ : ℝ} (hη : 0 < η) (hηξ : η ≤ ξ) :
    heatIntegral η ≤ heatIntegral ξ + (Real.pi^6/120)*Real.log (ξ/η) := by
  have hξ : 0 < ξ := hη.trans_le hηξ
  rw [heatIntegral_eq_gaussianTail hη, heatIntegral_eq_gaussianTail hξ,
    Real.log_div hξ.ne' hη.ne']
  have h := gaussianTail_log_corrected_monotone hη hξ hηξ
  linarith

#print axioms gaussianSlope_upper
#print axioms heatIntegral_log_growth
end BecknerOnofri.HighDim.EntropyTail
