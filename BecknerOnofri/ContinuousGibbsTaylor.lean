module

public import BecknerOnofri.ContinuousGibbs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Operator.Asymptotics

@[expose] public section

/-! The actual quadratic Taylor coefficient and cubic Banach-norm remainder
of the normalized Gibbs map on continuous real torus potentials. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.ContinuousGibbs

/-- Exact quadratic coefficient, including the mean correction. -/
def quadraticTerm {d : ℕ} (u : Space d) : Space d :=
  (1 / 2 : ℝ) • center d (u ^ 2) - mean d u • center d u

theorem quadraticTerm_apply {d : ℕ} (u : Space d) (x : Torus d) :
    quadraticTerm u x = (u x ^ 2 - mean d (u ^ 2)) / 2 - mean d u * (u x - mean d u) := by
  simp [quadraticTerm, center_apply]
  ring

theorem quadraticTerm_of_mean_zero {d : ℕ} {u : Space d} (hu : mean d u = 0) :
    quadraticTerm u = (1 / 2 : ℝ) • center d (u ^ 2) := by
  simp only [quadraticTerm, hu, zero_smul, sub_zero]

def quadraticPolynomial {d : ℕ} (u : Space d) : Space d := 1 + center d u + quadraticTerm u

def expCubicRemainder {d : ℕ} (u : Space d) : Space d :=
  exponential u - (1 + u + (1 / 2 : ℝ) • u ^ 2)

theorem expCubicRemainder_isBigO (d : ℕ) :
    expCubicRemainder =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 3) := by
  have hp : HasFPowerSeriesAt (@exponential d) (NormedSpace.expSeries ℝ (Space d)) 0 :=
    NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos (NormedSpace.expSeries_radius_pos ℝ (Space d))
  have hh := hp.isBigO_sub_partialSum_pow 3
  have he (u : Space d) : (NormedSpace.expSeries ℝ (Space d)).partialSum 3 u =
      1 + u + (1 / 2 : ℝ) • u ^ 2 := by
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, NormedSpace.expSeries_apply_eq,
      Nat.factorial]
  convert! hh using 1
  simp only [zero_add, he]
  rfl

private theorem norm_sq_isBigO_norm (d : ℕ) :
    (fun u : Space d => ‖u‖ ^ 2) =O[𝓝 0] (fun u => ‖u‖) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Space d) (by norm_num : (0 : ℝ) < 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u), abs_of_nonneg (sq_nonneg ‖u‖), one_mul]
  nlinarith [norm_nonneg u]

theorem quadraticTerm_isBigO (d : ℕ) :
    quadraticTerm =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 2) := by
  have hid : (fun u : Space d => u) =O[𝓝 0] (fun u => ‖u‖) := (isBigO_refl _ _).norm_right
  have hs : (fun u : Space d => u ^ 2) =O[𝓝 0] (fun u => ‖u‖ ^ 2) := by
    simpa only [pow_two] using hid.mul hid
  have hc := ((center d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hm := ((mean d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hc2 := (((center d).isBigO_comp (fun u : Space d => u ^ 2) (𝓝 0)).trans hs).const_smul_left (1/2:ℝ)
  have hmc : (fun u : Space d => mean d u • center d u) =O[𝓝 0] (fun u => ‖u‖ ^ 2) := by
    simpa only [smul_eq_mul, pow_two] using hm.smul hc
  exact hc2.sub hmc

private theorem mean_expCubicRemainder {d : ℕ} (u : Space d) :
    mean d (expCubicRemainder u) = partition u - (1 + mean d u + (1/2:ℝ) * mean d (u ^ 2)) := by
  simp only [expCubicRemainder, map_sub, map_add, map_smul, mean_one, smul_eq_mul, partition]

theorem quadratic_balance {d : ℕ} (u : Space d) :
    exponential u - partition u • quadraticPolynomial u =
      expCubicRemainder u - mean d (expCubicRemainder u) • quadraticPolynomial u -
        mean d u • quadraticTerm u - ((1/2:ℝ) * mean d (u ^ 2)) • (center d u + quadraticTerm u) := by
  rw [mean_expCubicRemainder]
  ext x
  simp only [expCubicRemainder, quadraticPolynomial,
    ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    ContinuousMap.pow_apply, smul_eq_mul, quadraticTerm_apply, center_apply]
  ring

theorem normalized_quadratic_remainder (d : ℕ) :
    (fun u : Space d => normalized u - quadraticPolynomial u) =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
  have hid : (fun u : Space d => u) =O[𝓝 0] (fun u => ‖u‖) := (isBigO_refl _ _).norm_right
  have hs : (fun u : Space d => u ^ 2) =O[𝓝 0] (fun u => ‖u‖ ^ 2) := by
    simpa only [pow_two] using hid.mul hid
  have hm := ((mean d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hc := ((center d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hq := quadraticTerm_isBigO d
  have hlq := hc.add (hq.trans (norm_sq_isBigO_norm d))
  have hmq := (((mean d).isBigO_comp (fun u : Space d => u ^ 2) (𝓝 0)).trans hs).const_mul_left (1/2:ℝ)
  have hPcont : ContinuousAt (@quadraticPolynomial d) 0 := by
    unfold quadraticPolynomial quadraticTerm
    fun_prop
  have hP : quadraticPolynomial =O[𝓝 (0 : Space d)] (fun _ => (1:ℝ)) := hPcont.isBigO
  have hR := expCubicRemainder_isBigO d
  have hr := ((mean d).isBigO_comp expCubicRemainder (𝓝 (0 : Space d))).trans hR
  have hRP : (fun u : Space d => mean d (expCubicRemainder u) • quadraticPolynomial u)
      =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by simpa only [smul_eq_mul, mul_one] using hr.smul hP
  have hmQ : (fun u : Space d => mean d u • quadraticTerm u)
      =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
    simpa only [smul_eq_mul, ← pow_succ'] using hm.smul hq
  have hqL : (fun u : Space d => ((1/2:ℝ) * mean d (u ^ 2)) • (center d u + quadraticTerm u))
      =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
    simpa only [smul_eq_mul, ← pow_succ] using hmq.smul hlq
  have hb := ((hR.sub hRP).sub hmQ).sub hqL
  have hi : (fun u : Space d => (partition u)⁻¹) =O[𝓝 0] (fun _ => (1:ℝ)) :=
    ((partition_analytic (0 : Space d)).continuousAt.inv₀ (partition_pos _).ne').isBigO
  have hfinal := hi.smul hb
  have he (u : Space d) : (partition u)⁻¹ •
      (expCubicRemainder u - mean d (expCubicRemainder u) • quadraticPolynomial u -
        mean d u • quadraticTerm u - ((1/2:ℝ) * mean d (u ^ 2)) • (center d u + quadraticTerm u)) =
      normalized u - quadraticPolynomial u := by
    rw [← quadratic_balance, smul_sub, smul_smul, inv_mul_cancel₀ (partition_pos u).ne', one_smul]
    rfl
  simpa only [he, smul_eq_mul, one_mul] using hfinal

#print axioms normalized_quadratic_remainder
end BecknerOnofri.HighDim.ContinuousGibbs
