import Legacy.BecknerOnofri.CircleHeatGeometry

/-! Strict circular heat monotonicity from the certified positive margins. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.CircleHeat
open CircleHeatDerivativeTail

theorem sine_series_pos_large {t x : ℝ} (ht : 1/4 ≤ t) (hx : x ∈ Ioo (0:ℝ) (1/2)) :
    0 < ∑' n : ℕ, sineTerm t n x := by
  have hs := summable_sineTerm (by linarith : 0 < t) x
  have htail := Summable.tsum_le_tsum (fun m => sineTerm_tail_lower (Ioo_subset_Icc_self hx) m)
    ((summable_fourierTail ht).mul_left (-(Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x))))
    ((summable_nat_add_iff 1).mpr hs)
  rw [tsum_mul_left] at htail
  change -(Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x))*fourierTail t ≤ _ at htail
  have hsin : 0 < Real.sin (2*Real.pi*x) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos,hx.1]) (by nlinarith [Real.pi_pos,hx.2])
  have hq : 0 < Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x) := mul_pos (Real.exp_pos _) hsin
  have hb := mul_le_mul_of_nonneg_left (fourierTail_le ht) hq.le
  have hz : sineTerm t 0 x = Real.exp (-Real.pi*t)*Real.sin (2*Real.pi*x) := by simp [sineTerm]
  rw [hs.tsum_eq_zero_add,hz]
  nlinarith only [htail,hb,hq]

theorem realHeat_strictAnti_large {t : ℝ} (ht : 1/4 ≤ t) :
    StrictAntiOn (realHeat t) (Icc (0:ℝ) (1/2)) := by
  have ht0 : 0 < t := by linarith
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro x _; exact (hasDerivAt_realHeat ht0 x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_realHeat ht0 x).deriv]
    exact mul_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) (sine_series_pos_large ht hx)

theorem finite_slope_sum_margin {A x : ℝ} (hA : 12 ≤ A) (hx : x ∈ Icc (0:ℝ) (1/4)) (N : ℕ) :
    (∑ m ∈ Finset.range N, (gaussianSlope A ((m:ℝ)+1-x)-gaussianSlope A ((m:ℝ)+1+x))) ≤
      (4/5)*gaussianSlope A x := by
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun m _ => gaussianSlope_difference_relative hA hx m)
  simp only [← Finset.mul_sum] at hsum
  have hp := (summable_poissonTail hA).sum_le_tsum (Finset.range N) (fun m _ => by dsimp [poissonTerm]; positivity)
  have hscale := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ (25/4)*A)
  change (25/4)*A*(∑ m ∈ Finset.range N, poissonTerm A m) ≤ (25/4)*A*poissonTail A at hscale
  have hbound : (25/4)*A*(∑ m ∈ Finset.range N, poissonTerm A m) ≤ 4/5 :=
    hscale.trans ((poissonTail_scaled_le hA).trans (by norm_num))
  have hn : 0 ≤ x*Real.exp (-A*x^2) := mul_nonneg hx.1 (Real.exp_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hbound hn
  change _ ≤ (4/5)*(x*Real.exp (-A*x^2))
  nlinarith only [hsum,hh]

def residualGaussian (A : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  finiteSymmetricGaussian A N x-(1/5)*Real.exp (-A*x^2)

theorem hasDerivAt_residualGaussian (A : ℝ) (N : ℕ) (x : ℝ) :
    HasDerivAt (residualGaussian A N)
      (2*A*(∑ m ∈ Finset.range N, (gaussianSlope A ((m:ℝ)+1-x)-gaussianSlope A ((m:ℝ)+1+x)))-
        (8/5)*A*gaussianSlope A x) x := by
  have hh := (hasDerivAt_finiteSymmetricGaussian A N x).sub
    (((((hasDerivAt_id x).pow 2).const_mul (-A)).exp).const_mul (1/5))
  convert! hh using 1
  dsimp [gaussianSlope]
  ring

theorem residualGaussian_antitone {A : ℝ} (hA : 12 ≤ A) (N : ℕ) :
    AntitoneOn (residualGaussian A N) (Icc (0:ℝ) (1/4)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro x _; exact (hasDerivAt_residualGaussian A N x).continuousAt.continuousWithinAt
  · intro x _; exact (hasDerivAt_residualGaussian A N x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_residualGaussian A N x).deriv]
    have hh := finite_slope_sum_margin hA (interior_subset hx) N
    nlinarith

theorem poisson_residual_antitone {A : ℝ} (hA : 12 ≤ A) :
    AntitoneOn (fun x => poissonSeries A x-(1/5)*Real.exp (-A*x^2)) (Icc (0:ℝ) (1/4)) := by
  apply antitoneOn_of_frequently_antitoneOn_of_tendsto (l := atTop) (F := residualGaussian A)
    ((Filter.Eventually.of_forall (fun N => residualGaussian_antitone hA N)).frequently)
  intro x _
  exact (finiteSymmetricGaussian_tendsto (by linarith : 0 < A) x).sub tendsto_const_nhds

theorem poissonSeries_strictAnti_near {A : ℝ} (hA : 12 ≤ A) :
    StrictAntiOn (poissonSeries A) (Icc (0:ℝ) (1/4)) := by
  intro x hx y hy hxy
  have hh := poisson_residual_antitone hA hx hy hxy.le
  have hsq : x^2 < y^2 := (sq_lt_sq₀ hx.1 hy.1).mpr hxy
  have he : Real.exp (-A*y^2) < Real.exp (-A*x^2) := Real.exp_lt_exp.mpr (by nlinarith)
  dsimp only at hh
  linarith

theorem gaussianSlope_strictAnti {A : ℝ} (hA : 12 ≤ A) :
    StrictAntiOn (gaussianSlope A) (Ici (1/4:ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro x _; exact (hasDerivAt_gaussianSlope A x).continuousAt.continuousWithinAt
  · intro x hx
    have hxq : 1/4 ≤ x := interior_subset hx
    have hx2 : (1/4:ℝ)^2 ≤ x^2 := (sq_le_sq₀ (by norm_num) (by linarith)).mpr hxq
    rw [(hasDerivAt_gaussianSlope A x).deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by nlinarith)

theorem adjacentGaussian_strictAnti {A : ℝ} (hA : 12 ≤ A) (m : ℕ) :
    StrictAntiOn (adjacentGaussian A m) (Icc (1/4:ℝ) (1/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro x _; exact (hasDerivAt_adjacentGaussian A m x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hh := gaussianSlope_strictAnti hA
      (show (m:ℝ)+x ∈ Ici (1/4:ℝ) by change 1/4 ≤ (m:ℝ)+x; linarith [Nat.cast_nonneg (α := ℝ) m,hx.1])
      (show (m:ℝ)+1-x ∈ Ici (1/4:ℝ) by change 1/4 ≤ (m:ℝ)+1-x; linarith [Nat.cast_nonneg (α := ℝ) m,hx.2])
      (show (m:ℝ)+x < (m:ℝ)+1-x by linarith [hx.2])
    rw [(hasDerivAt_adjacentGaussian A m x).deriv]
    exact mul_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hh)

theorem poissonSeries_strictAnti_far {A : ℝ} (hA : 12 ≤ A) :
    StrictAntiOn (poissonSeries A) (Icc (1/4:ℝ) (1/2)) := by
  intro x hx y hy hxy
  rw [← (adjacentGaussian_hasSum (by linarith : 0 < A) x).tsum_eq,
    ← (adjacentGaussian_hasSum (by linarith : 0 < A) y).tsum_eq]
  exact Summable.tsum_lt_tsum (fun m => adjacentGaussian_antitone hA m hx hy hxy.le)
    (adjacentGaussian_strictAnti hA 0 hx hy hxy)
    (adjacentGaussian_hasSum (by linarith) y).summable (adjacentGaussian_hasSum (by linarith) x).summable

theorem poissonSeries_strictAnti {A : ℝ} (hA : 12 ≤ A) :
    StrictAntiOn (poissonSeries A) (Icc (0:ℝ) (1/2)) := by
  intro x hx y hy hxy
  by_cases hyq : y ≤ 1/4
  · exact poissonSeries_strictAnti_near hA ⟨hx.1,hxy.le.trans hyq⟩ ⟨hy.1,hyq⟩ hxy
  by_cases hxq : 1/4 ≤ x
  · exact poissonSeries_strictAnti_far hA ⟨hxq,hx.2⟩ ⟨hxq.trans hxy.le,hy.2⟩ hxy
  exact lt_trans
    (poissonSeries_strictAnti_far hA (show (1/4:ℝ) ∈ Icc (1/4:ℝ) (1/2) by norm_num) ⟨by linarith,hy.2⟩ (by linarith))
    (poissonSeries_strictAnti_near hA ⟨hx.1,by linarith⟩ (show (1/4:ℝ) ∈ Icc (0:ℝ) (1/4) by norm_num) (by linarith))

theorem realHeat_strictAnti_small {t : ℝ} (ht : 0 < t) (htq : t ≤ 1/4) :
    StrictAntiOn (realHeat t) (Icc (0:ℝ) (1/2)) := by
  have hA : 12 ≤ Real.pi/t := (le_div_iff₀ ht).mpr (by nlinarith [Real.pi_gt_three])
  intro x hx y hy hxy
  unfold realHeat
  rw [theta_coe_eq_shifted_gaussian ht,theta_coe_eq_shifted_gaussian ht,Complex.ofReal_re,Complex.ofReal_re]
  apply mul_lt_mul_of_pos_left _ (by positivity)
  simpa only [poissonSeries,neg_div] using poissonSeries_strictAnti hA hx hy hxy

theorem realHeat_strictAnti {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (realHeat t) (Icc (0:ℝ) (1/2)) := by
  by_cases h : t ≤ 1/4
  · exact realHeat_strictAnti_small ht h
  · exact realHeat_strictAnti_large (by linarith)

#print axioms realHeat_strictAnti
end Legacy.BecknerOnofri.CircleHeat
