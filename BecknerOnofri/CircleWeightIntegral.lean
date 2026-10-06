module

public import BecknerOnofri.CircleWeightSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Identification of the positive-series weight with the exact integral
appearing after integration of the Poisson-flow dissipation. -/
noncomputable section
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CircleScalar

theorem weight_integral (n : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    weight n t=∫ s in (0:ℝ)..1,s^n/(1-t^2*s) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let F : ℕ → ℝ → ℝ := fun j s => t^(2*j)*s^(n+j)
  have hi (j : ℕ) : Integrable (F j) μ := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
    exact ((continuous_id.pow (n+j)).const_mul (t^(2*j))).intervalIntegrable 0 1
  have hint (j : ℕ) : (∫ s,F j s ∂μ)=t^(2*j)/(n+j+1:ℝ) := by
    change (∫ s in Ioc (0:ℝ) 1,t^(2*j)*s^(n+j))=_
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),intervalIntegral.integral_const_mul,
      integral_pow]
    simp [div_eq_mul_inv]
  have hnorm (j : ℕ) : (∫ s,‖F j s‖ ∂μ)=t^(2*j)/(n+j+1:ℝ) := by
    rw [← hint]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs,abs_of_nonneg]
    exact mul_nonneg (pow_nonneg ht _) (pow_nonneg hs.1.le _)
  have hsumNorm : Summable (fun j => ∫ s,‖F j s‖ ∂μ) := by
    simp_rw [hnorm]
    exact weight_summable n ht ht1
  have hswap := integral_tsum_of_summable_integral_norm hi hsumNorm
  have he : (∫ s,∑' j,F j s ∂μ)=∫ s,s^n/(1-t^2*s) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hz : 0≤t^2*s := mul_nonneg (sq_nonneg t) hs.1.le
    have hz1 : t^2*s<1 := by
      have hle := mul_le_mul_of_nonneg_left hs.2 (sq_nonneg t)
      nlinarith
    have hpoint (j : ℕ) : F j s=s^n*(t^2*s)^j := by
      dsimp only [F]
      rw [mul_pow,← pow_mul,pow_add]
      ring
    simp_rw [hpoint]
    rw [tsum_mul_left,tsum_geometric_of_lt_one hz hz1]
    rfl
  rw [he] at hswap
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  change weight n t=∫ s,s^n/(1-t^2*s) ∂μ
  rw [← hswap]
  simp_rw [hint]
  rfl

#print axioms weight_integral
end BecknerOnofri.HighDim.CircleScalar
