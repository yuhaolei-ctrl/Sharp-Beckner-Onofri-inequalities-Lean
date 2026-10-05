import BecknerOnofri.ContinuousGibbsTaylor

/-! The genuine cubic normalized-Gibbs coefficient with a fourth-order uniform-norm remainder. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.ContinuousGibbs

def cubicTerm {d : ℕ} (u : Space d) : Space d :=
  (1/6:ℝ) • center d (u ^ 3) - mean d u • quadraticTerm u -
    ((1/2:ℝ) * mean d (u ^ 2)) • center d u

def cubicPolynomial {d : ℕ} (u : Space d) : Space d := quadraticPolynomial u + cubicTerm u

def expQuarticRemainder {d : ℕ} (u : Space d) : Space d :=
  exponential u - (1 + u + (1/2:ℝ) • u ^ 2 + (1/6:ℝ) • u ^ 3)

theorem cubicTerm_apply {d : ℕ} (u : Space d) (x : Torus d) :
    cubicTerm u x = (u x ^ 3 - mean d (u ^ 3))/6 - mean d u * quadraticTerm u x -
      (mean d (u ^ 2)/2) * (u x - mean d u) := by
  simp [cubicTerm, center_apply]
  ring

theorem center_eq_self_of_mean_zero {d : ℕ} {u : Space d} (hu : mean d u = 0) : center d u = u := by
  ext x
  simp only [center_apply, hu, sub_zero]

theorem cubicTerm_of_mean_zero {d : ℕ} {u : Space d} (hu : mean d u = 0) :
    cubicTerm u = (1/6:ℝ) • center d (u ^ 3) - ((1/2:ℝ) * mean d (u ^ 2)) • u := by
  simp only [cubicTerm, hu, zero_smul, sub_zero, center_eq_self_of_mean_zero hu]

private theorem norm_succ_isBigO (d n : ℕ) :
    (fun u : Space d => ‖u‖ ^ (n+1)) =O[𝓝 0] (fun u => ‖u‖ ^ n) := by
  apply isBigO_iff.mpr
  refine ⟨1, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Space d) (by norm_num : (0 : ℝ) < 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hu
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg u) _), one_mul, pow_succ]
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg u) n) (norm_nonneg u))]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg u) n) hu'.le

theorem expQuarticRemainder_isBigO (d : ℕ) :
    expQuarticRemainder =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 4) := by
  have hp : HasFPowerSeriesAt (@exponential d) (NormedSpace.expSeries ℝ (Space d)) 0 :=
    NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos (NormedSpace.expSeries_radius_pos ℝ (Space d))
  have hh := hp.isBigO_sub_partialSum_pow 4
  have he (u : Space d) : (NormedSpace.expSeries ℝ (Space d)).partialSum 4 u =
      1 + u + (1/2:ℝ) • u ^ 2 + (1/6:ℝ) • u ^ 3 := by
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, NormedSpace.expSeries_apply_eq,
      Nat.factorial]
  convert! hh using 1
  simp only [zero_add, he]
  rfl

theorem cubicTerm_isBigO (d : ℕ) : cubicTerm =O[𝓝 (0 : Space d)] (fun u => ‖u‖ ^ 3) := by
  have hid : (fun u : Space d => u) =O[𝓝 0] (fun u => ‖u‖) := (isBigO_refl _ _).norm_right
  have hs : (fun u : Space d => u ^ 2) =O[𝓝 0] (fun u => ‖u‖ ^ 2) := by
    simpa only [pow_two] using hid.mul hid
  have hcub : (fun u : Space d => u ^ 3) =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
    simpa only [← pow_succ] using hs.mul hid
  have hm := ((mean d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hc := ((center d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hq := quadraticTerm_isBigO d
  have hm2 := (((mean d).isBigO_comp (fun u : Space d => u ^ 2) (𝓝 0)).trans hs).const_mul_left (1/2:ℝ)
  have hbase := (((center d).isBigO_comp (fun u : Space d => u ^ 3) (𝓝 0)).trans hcub).const_smul_left (1/6:ℝ)
  have hmQ : (fun u : Space d => mean d u • quadraticTerm u) =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
    simpa only [smul_eq_mul, ← pow_succ'] using hm.smul hq
  have hmL : (fun u : Space d => ((1/2:ℝ) * mean d (u ^ 2)) • center d u)
      =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
    simpa only [smul_eq_mul, ← pow_succ] using hm2.smul hc
  exact (hbase.sub hmQ).sub hmL

private theorem mean_expQuarticRemainder {d : ℕ} (u : Space d) :
    mean d (expQuarticRemainder u) =
      partition u - (1 + mean d u + (1/2:ℝ) * mean d (u ^ 2) + (1/6:ℝ) * mean d (u ^ 3)) := by
  simp only [expQuarticRemainder, map_sub, map_add, map_smul, mean_one, smul_eq_mul, partition]

theorem cubic_balance {d : ℕ} (u : Space d) :
    exponential u - partition u • cubicPolynomial u =
      expQuarticRemainder u - mean d (expQuarticRemainder u) • cubicPolynomial u -
        mean d u • cubicTerm u - ((1/2:ℝ) * mean d (u ^ 2)) • (quadraticTerm u + cubicTerm u) -
        ((1/6:ℝ) * mean d (u ^ 3)) • (center d u + quadraticTerm u + cubicTerm u) := by
  rw [mean_expQuarticRemainder]
  ext x
  simp only [expQuarticRemainder, cubicPolynomial, quadraticPolynomial,
    ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    ContinuousMap.pow_apply, smul_eq_mul, cubicTerm_apply, quadraticTerm_apply, center_apply]
  ring

theorem normalized_cubic_remainder (d : ℕ) :
    (fun u : Space d => normalized u - cubicPolynomial u) =O[𝓝 0] (fun u => ‖u‖ ^ 4) := by
  have hid : (fun u : Space d => u) =O[𝓝 0] (fun u => ‖u‖) := (isBigO_refl _ _).norm_right
  have hs : (fun u : Space d => u ^ 2) =O[𝓝 0] (fun u => ‖u‖ ^ 2) := by
    simpa only [pow_two] using hid.mul hid
  have h3 : (fun u : Space d => u ^ 3) =O[𝓝 0] (fun u => ‖u‖ ^ 3) := by
    simpa only [← pow_succ] using hs.mul hid
  have hm := ((mean d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hc := ((center d).isBigO_comp (fun u : Space d => u) (𝓝 0)).trans hid
  have hq := quadraticTerm_isBigO d
  have ht := cubicTerm_isBigO d
  have hqt := hq.add (ht.trans (norm_succ_isBigO d 2))
  have hlqt := hc.add (hqt.trans (by simpa using norm_succ_isBigO d 1))
  have hm2 := (((mean d).isBigO_comp (fun u : Space d => u ^ 2) (𝓝 0)).trans hs).const_mul_left (1/2:ℝ)
  have hm3 := (((mean d).isBigO_comp (fun u : Space d => u ^ 3) (𝓝 0)).trans h3).const_mul_left (1/6:ℝ)
  have hPcont : ContinuousAt (@cubicPolynomial d) 0 := by
    unfold cubicPolynomial cubicTerm quadraticPolynomial quadraticTerm
    fun_prop
  have hP : cubicPolynomial =O[𝓝 (0 : Space d)] (fun _ => (1:ℝ)) := hPcont.isBigO
  have hR := expQuarticRemainder_isBigO d
  have hr := ((mean d).isBigO_comp expQuarticRemainder (𝓝 (0 : Space d))).trans hR
  have hRP : (fun u : Space d => mean d (expQuarticRemainder u) • cubicPolynomial u)
      =O[𝓝 0] (fun u => ‖u‖ ^ 4) := by simpa only [smul_eq_mul, mul_one] using hr.smul hP
  have hmT : (fun u : Space d => mean d u • cubicTerm u)
      =O[𝓝 0] (fun u => ‖u‖ ^ 4) := by
    simpa only [smul_eq_mul, ← pow_succ'] using hm.smul ht
  have hqQT : (fun u : Space d => ((1/2:ℝ) * mean d (u ^ 2)) • (quadraticTerm u + cubicTerm u))
      =O[𝓝 0] (fun u => ‖u‖ ^ 4) := by
    simpa only [smul_eq_mul, ← pow_add] using hm2.smul hqt
  have htLQT : (fun u : Space d => ((1/6:ℝ) * mean d (u ^ 3)) •
      (center d u + quadraticTerm u + cubicTerm u)) =O[𝓝 0] (fun u => ‖u‖ ^ 4) := by
    simpa only [smul_eq_mul, ← pow_succ, add_assoc] using hm3.smul hlqt
  have hb := (((hR.sub hRP).sub hmT).sub hqQT).sub htLQT
  have hi : (fun u : Space d => (partition u)⁻¹) =O[𝓝 0] (fun _ => (1:ℝ)) :=
    ((partition_analytic (0 : Space d)).continuousAt.inv₀ (partition_pos _).ne').isBigO
  have hfinal := hi.smul hb
  have he (u : Space d) : (partition u)⁻¹ •
      (expQuarticRemainder u - mean d (expQuarticRemainder u) • cubicPolynomial u -
        mean d u • cubicTerm u - ((1/2:ℝ) * mean d (u ^ 2)) • (quadraticTerm u + cubicTerm u) -
        ((1/6:ℝ) * mean d (u ^ 3)) • (center d u + quadraticTerm u + cubicTerm u)) =
      normalized u - cubicPolynomial u := by
    rw [← cubic_balance, smul_sub, smul_smul, inv_mul_cancel₀ (partition_pos u).ne', one_smul]
    rfl
  simpa only [he, smul_eq_mul, one_mul] using hfinal

/-- On mean-zero potentials these are the usual centered moment coefficients. -/
theorem cubicPolynomial_of_mean_zero {d : ℕ} {u : Space d} (hu : mean d u = 0) :
    cubicPolynomial u = 1 + u + (1/2:ℝ) • center d (u ^ 2) +
      (1/6:ℝ) • center d (u ^ 3) - (mean d (u ^ 2)/2) • u := by
  rw [cubicPolynomial, quadraticPolynomial, quadraticTerm_of_mean_zero hu,
    cubicTerm_of_mean_zero hu, center_eq_self_of_mean_zero hu]
  have hscalar : (1/2:ℝ) * mean d (u ^ 2) = mean d (u ^ 2)/2 := by ring
  rw [hscalar]
  abel

/-- A genuine uniform-norm fourth-order Taylor estimate, with one neighborhood
and constant valid simultaneously for every mean-zero continuous potential. -/
theorem normalized_cubic_bound_mean_zero (d : ℕ) :
    ∃ C > 0, ∃ ε > 0, ∀ u : Space d, ‖u‖ < ε → mean d u = 0 →
      ‖normalized u - (1 + u + (1/2:ℝ) • center d (u ^ 2) +
        (1/6:ℝ) • center d (u ^ 3) - (mean d (u ^ 2)/2) • u)‖ ≤ C * ‖u‖ ^ 4 := by
  obtain ⟨C, hC, h⟩ := (normalized_cubic_remainder d).exists_pos
  rw [IsBigOWith_def] at h
  obtain ⟨ε, hε, hbound⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨C, hC, ε, hε, ?_⟩
  intro u hu hm
  have hb := hbound (y := u) (by simpa only [dist_zero_right] using hu)
  rw [cubicPolynomial_of_mean_zero hm] at hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg u) 4)] using hb

#print axioms normalized_cubic_remainder
#print axioms normalized_cubic_bound_mean_zero
end BecknerOnofri.HighDim.ContinuousGibbs
