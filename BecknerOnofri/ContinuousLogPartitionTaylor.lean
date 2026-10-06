module

public import BecknerOnofri.ContinuousGibbsCubic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! The actual centered logarithmic partition function through quartic order,
with a fifth-order remainder in the Banach norm of continuous potentials. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.ContinuousGibbs

def centeredLogPartition {d : ℕ} (u : Space d) : ℝ := Real.log (partition (center d u))

def centeredMoment {d : ℕ} (n : ℕ) (u : Space d) : ℝ := mean d ((center d u) ^ n)

def quarticLogPolynomial {d : ℕ} (u : Space d) : ℝ :=
  centeredMoment 2 u / 2 + centeredMoment 3 u / 6 + centeredMoment 4 u / 24 -
    (centeredMoment 2 u)^2 / 8

theorem mean_center {d : ℕ} (u : Space d) : mean d (center d u) = 0 := by
  change (∫ x, u x - mean d u ∂torusMeasure d) = 0
  rw [integral_sub (integrable d u) (integrable_const _)]
  simp [mean_apply]

theorem logPartition_eq_centeredLogPartition {d : ℕ} (u : Space d) :
    logPartition u = (centeredLogPartition u : EReal) := by
  have he (x : Torus d) : Real.exp (centered u x) = exponential (center d u) x := by
    simp only [exponential_apply, center_apply, centered, mean_apply]
  have hi : Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) := by
    simpa only [he] using integrable d (exponential (center d u))
  unfold logPartition
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  simp only [he]
  change ENNReal.log (ENNReal.ofReal (partition (center d u))) = _
  rw [ENNReal.log_ofReal_of_pos (partition_pos _)]
  rfl

theorem norm_power_succ_isBigO (d n : ℕ) :
    (fun u : Space d => ‖u‖ ^ (n+1)) =O[𝓝 0] (fun u => ‖u‖ ^ n) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Space d) (by norm_num : (0 : ℝ) < 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg u) _), one_mul, pow_succ]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg u) n) (norm_nonneg u))]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg u) n) hu'.le

theorem centeredMoment_isBigO (d n : ℕ) :
    centeredMoment n =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ n) := by
  have hid : (fun u : Space d => u) =O[𝓝 0] (fun u => ‖u‖) := (isBigO_refl _ _).norm_right
  have hc := ((center d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  exact ((mean d).isBigO_comp (fun u : Space d => (center d u)^n) (𝓝 0)).trans (hc.pow n)

def expFifthRemainder {d : ℕ} (u : Space d) : Space d :=
  exponential u - (1 + u + (1/2:ℝ) • u ^ 2 + (1/6:ℝ) • u ^ 3 + (1/24:ℝ) • u ^ 4)

theorem expFifthRemainder_isBigO (d : ℕ) :
    expFifthRemainder =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 5) := by
  have hp : HasFPowerSeriesAt (@exponential d) (NormedSpace.expSeries ℝ (Space d)) 0 :=
    NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos (NormedSpace.expSeries_radius_pos ℝ (Space d))
  have hh := hp.isBigO_sub_partialSum_pow 5
  have he (u : Space d) : (NormedSpace.expSeries ℝ (Space d)).partialSum 5 u =
      1 + u + (1/2:ℝ) • u ^ 2 + (1/6:ℝ) • u ^ 3 + (1/24:ℝ) • u ^ 4 := by
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, NormedSpace.expSeries_apply_eq,
      Nat.factorial]
  convert! hh using 1
  simp only [zero_add, he]
  rfl

theorem centered_remainder_isBigO {d n : ℕ} {R : Space d → Space d}
    (hR : R =O[𝓝 0] (fun u => ‖u‖ ^ n)) :
    (fun u : Space d => mean d (R (center d u))) =O[𝓝 0] (fun u => ‖u‖ ^ n) := by
  have hid : (fun u : Space d => u) =O[𝓝 0] (fun u => ‖u‖) := (isBigO_refl _ _).norm_right
  have hc := ((center d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hct : Tendsto (center d) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (center d).continuous.tendsto (0 : Space d)
  exact ((mean d).isBigO_comp (fun u : Space d => R (center d u)) (𝓝 0)).trans
    ((hR.comp_tendsto hct).trans (hc.norm_left.pow n))

def centeredPartitionIncrement {d : ℕ} (u : Space d) : ℝ := partition (center d u) - 1

theorem centered_partition_second_remainder (d : ℕ) :
    (fun u : Space d => centeredPartitionIncrement u - centeredMoment 2 u / 2)
      =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
  have h := centered_remainder_isBigO (expCubicRemainder_isBigO d)
  have he (u : Space d) : mean d (expCubicRemainder (center d u)) =
      centeredPartitionIncrement u - centeredMoment 2 u / 2 := by
    simp only [expCubicRemainder, map_sub, map_add, map_smul, mean_one, mean_center, add_zero,
      smul_eq_mul, centeredPartitionIncrement, centeredMoment, partition]
    ring
  simpa only [he] using h

theorem centeredPartitionIncrement_isBigO (d : ℕ) :
    centeredPartitionIncrement =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 2) := by
  have hq := (centeredMoment_isBigO d 2).const_mul_left (1/2:ℝ)
  have hr := (centered_partition_second_remainder d).trans (norm_power_succ_isBigO d 2)
  convert! hr.add hq using 1
  ext u
  ring

theorem centered_partition_fourth_remainder (d : ℕ) :
    (fun u : Space d => centeredPartitionIncrement u -
      (centeredMoment 2 u / 2 + centeredMoment 3 u / 6 + centeredMoment 4 u / 24))
      =O[𝓝 0] (fun u => ‖u‖ ^ 5) := by
  have h := centered_remainder_isBigO (expFifthRemainder_isBigO d)
  have he (u : Space d) : mean d (expFifthRemainder (center d u)) =
      centeredPartitionIncrement u -
        (centeredMoment 2 u / 2 + centeredMoment 3 u / 6 + centeredMoment 4 u / 24) := by
    simp only [expFifthRemainder, map_sub, map_add, map_smul, mean_one, mean_center, add_zero,
      smul_eq_mul, centeredPartitionIncrement, centeredMoment, partition]
    ring
  simpa only [he] using h

/-- An actual scalar logarithm estimate, used only after controlling the true partition. -/
theorem log_one_add_quadratic_remainder :
    (fun x : ℝ => Real.log (1+x) - x + x^2/2) =O[𝓝 0] (fun x => ‖x‖^3) := by
  apply IsBigO.of_bound 2
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1/2)] with x hx
  have hx' : |x| < 1/2 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
  have hl := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 2
  have he : (∑ i ∈ Finset.range 2, (-x)^(i+1)/(i+1)) + Real.log (1-(-x)) =
      Real.log (1+x)-x+x^2/2 := by
    simp [Finset.sum_range_succ]
    ring
  rw [he, abs_neg] at hl
  have hb : |x|^3/(1-|x|) ≤ 2*|x|^3 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-|x|)).mpr
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  simpa [Real.norm_eq_abs, abs_pow] using hl.trans hb

theorem centeredLogPartition_quartic_remainder (d : ℕ) :
    (fun u : Space d => centeredLogPartition u - quarticLogPolynomial u)
      =O[𝓝 0] (fun u => ‖u‖ ^ 5) := by
  have hx := centeredPartitionIncrement_isBigO d
  have hxt : Tendsto (@centeredPartitionIncrement d) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (@centeredPartitionIncrement d) 0 := by
      unfold centeredPartitionIncrement
      exact (((partition_analytic _).continuousAt).comp (center d).continuous.continuousAt).sub continuousAt_const
    simpa [centeredPartitionIncrement] using hc.tendsto
  have hlog6 := (log_one_add_quadratic_remainder.comp_tendsto hxt).trans (hx.norm_left.pow 3)
  have hlog5 : (fun u : Space d => Real.log (1+centeredPartitionIncrement u) - centeredPartitionIncrement u +
      (centeredPartitionIncrement u)^2/2) =O[𝓝 0] (fun u => ‖u‖ ^ 5) := by
    have hh : (fun u : Space d => Real.log (1+centeredPartitionIncrement u) - centeredPartitionIncrement u +
        (centeredPartitionIncrement u)^2/2) =O[𝓝 0] (fun u => ‖u‖ ^ 6) := by
      convert! hlog6 using 1
      funext u
      simp only [← pow_mul]
    exact hh.trans (norm_power_succ_isBigO d 5)
  have hq : (fun u : Space d => centeredMoment 2 u / 2) =O[𝓝 0] (fun u => ‖u‖ ^ 2) := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using (centeredMoment_isBigO d 2).const_mul_left (1/2:ℝ)
  have hdiff := centered_partition_second_remainder d
  have hsq : (fun u : Space d => (centeredPartitionIncrement u)^2 - (centeredMoment 2 u / 2)^2)
      =O[𝓝 0] (fun u => ‖u‖ ^ 5) := by
    have hh := hdiff.mul (hx.add hq)
    convert! hh using 1
    · ext u
      ring
    · ext u
      ring
  have hsqhalf := hsq.const_mul_left (1/2:ℝ)
  have hfinal := (hlog5.add (centered_partition_fourth_remainder d)).sub hsqhalf
  convert! hfinal using 1
  ext u
  simp only [centeredLogPartition, quarticLogPolynomial, centeredPartitionIncrement]
  have harg : 1 + (partition (center d u) - 1) = partition (center d u) := by ring
  rw [harg]
  ring

/-- Uniform fifth-order remainder for the actual log partition of every
mean-zero continuous potential in one fixed neighborhood. -/
theorem logPartition_quartic_bound_mean_zero (d : ℕ) :
    ∃ C > 0, ∃ ε > 0, ∀ u : Space d, ‖u‖ < ε → mean d u = 0 →
      |Real.log (partition u) - (mean d (u ^ 2)/2 + mean d (u ^ 3)/6 +
        mean d (u ^ 4)/24 - (mean d (u ^ 2))^2/8)| ≤ C * ‖u‖ ^ 5 := by
  obtain ⟨C, hC, h⟩ := (centeredLogPartition_quartic_remainder d).exists_pos
  rw [IsBigOWith_def] at h
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨C, hC, ε, hε, ?_⟩
  intro u hu hm
  have hb := hbound (y := u) (by simpa only [dist_zero_right] using hu)
  simpa only [centeredLogPartition, quarticLogPolynomial, centeredMoment,
    center_eq_self_of_mean_zero hm, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg u) 5)] using hb

#print axioms centeredLogPartition_quartic_remainder
#print axioms logPartition_quartic_bound_mean_zero
#print axioms logPartition_eq_centeredLogPartition
end BecknerOnofri.HighDim.ContinuousGibbs
