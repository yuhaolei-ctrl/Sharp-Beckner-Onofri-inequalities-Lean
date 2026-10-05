module

public import BecknerOnofri.LocalHighEnergy
public import BecknerOnofri.LocalConstants

@[expose] public section

/-! Strict local negativity for the actual first-shell/higher-mode decomposition.
The partition is the actual Haar integral; the higher energy is the genuine
Fourier Sobolev energy. Fourier support and all Qσ bounds are proved analytically.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment

/-- The source functional in the first-shell plus higher-mode variables. -/
def localSplitPressure (t : Fin 12 → ℝ) (w : TorusL2 12) : ℝ :=
  Real.log (∫ x, Real.exp (firstShellPotential t x + (w x).re) ∂torusMeasure 12) -
    (∑ i, t i ^ 2) - criticalEnergy w / 2

def localExitD : ℝ := 1 - Real.exp (187 / 105 : ℝ) / 64

def localExitCoefficient : ℝ := -(6 / 25 : ℝ) +
  (12 / 64 : ℝ) * Real.exp (6 / 49 : ℝ) / localExitD

lemma localExitD_pos : 0 < localExitD := local_exit_denominator_pos
lemma localExitCoefficient_neg : localExitCoefficient < 0 := by
  unfold localExitCoefficient localExitD
  linarith [local_exit_ratio_lt]

lemma local_neighborhood_sum_bounds (t : Fin 12 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14) :
    2 * (∑ i, t i) + 2 * (1 / 30 : ℝ) ≤ 187 / 105 ∧
    2 * (∑ i, t i ^ 2) ≤ (6 / 49 : ℝ) := by
  have hs : (∑ i, t i) ≤ (12 : ℝ) * (1 / 14) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hta i)
  have hss : (∑ i, t i ^ 2) ≤ (12 : ℝ) * (1 / 14) ^ 2 := by
    simpa using Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => pow_le_pow_left₀ (ht i) (hta i) 2)
  constructor <;> linarith

lemma higher_real_aestronglyMeasurable (w : TorusL2 12) :
    AEStronglyMeasurable (fun x => (w x).re) (torusMeasure 12) :=
  Complex.continuous_re.comp_aestronglyMeasurable (Lp.memLp w).1

lemma localSplitPressure_preliminary_bound (t : Fin 12 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14)
    (w : TorusL2 12) (hw : CriticalSobolev w) (hh : HasOnlyHigherModes w)
    (hbound : ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ)) :
    localSplitPressure t w ≤ -(6 / 25 : ℝ) * ∑ i, t i ^ 4 +
      (∫ x, firstShellTilt t x * (w x).re ∂torusMeasure 12) -
      localExitD / 2 * criticalEnergy w := by
  have hlog := firstShell_add_log_partition_bound t ht (fun x => (w x).re) (1 / 30)
    (higher_real_aestronglyMeasurable w) (by norm_num) hbound
  have hfirst := firstShell_log_partition_quartic t ht (fun i => (hta i).trans (by norm_num))
  have hsq := higher_real_sq_integral_le_energy w hw hh
  have hexp := Real.exp_le_exp.mpr (local_neighborhood_sum_bounds t ht hta).1
  have he := mul_le_mul hexp hsq
    (integral_nonneg (fun x => sq_nonneg (w x).re)) (Real.exp_nonneg _)
  have henergy := energy_nonneg w
  unfold localSplitPressure localExitD
  nlinarith

lemma localSplitPressure_quartic_bound (t : Fin 12 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14)
    (w : TorusL2 12) (hw : CriticalSobolev w) (hh : HasOnlyHigherModes w)
    (hbound : ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ)) :
    localSplitPressure t w ≤ localExitCoefficient * ∑ i, t i ^ 4 := by
  have hpre := localSplitPressure_preliminary_bound t ht hta w hw hh hbound
  have hpair := higher_pairing_quadratic_bound w hw hh t ht localExitD localExitD_pos
  have hq := localQsigma_quartic_bound t ht
  have hquart : 0 ≤ ∑ i, t i ^ 4 := Finset.sum_nonneg (fun i _ => by positivity)
  have hexp := Real.exp_le_exp.mpr (local_neighborhood_sum_bounds t ht hta).2
  have hq' : localQsigma t ≤ (3 / 8 : ℝ) * Real.exp (6 / 49 : ℝ) * ∑ i, t i ^ 4 := by
    exact hq.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num)) hquart)
  have hdiv := div_le_div_of_nonneg_right hq'
    (show (0 : ℝ) ≤ 2 * localExitD from mul_nonneg (by norm_num) localExitD_pos.le)
  have he : ((3 / 8 : ℝ) * Real.exp (6 / 49 : ℝ) * ∑ i, t i ^ 4) / (2 * localExitD) =
      ((12 / 64 : ℝ) * Real.exp (6 / 49 : ℝ) / localExitD) * ∑ i, t i ^ 4 := by ring
  rw [he] at hdiv
  unfold localExitCoefficient
  linarith

lemma localSplitPressure_lt_zero_of_firstShell_ne (t : Fin 12 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14) (htne : t ≠ 0)
    (w : TorusL2 12) (hw : CriticalSobolev w) (hh : HasOnlyHigherModes w)
    (hbound : ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ)) :
    localSplitPressure t w < 0 := by
  have hquart : 0 < ∑ i, t i ^ 4 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp htne
    apply Finset.sum_pos' (fun i _ => pow_nonneg (ht i) 4)
    exact ⟨i, Finset.mem_univ i, pow_pos (lt_of_le_of_ne (ht i) (Ne.symm hi)) 4⟩
  exact (localSplitPressure_quartic_bound t ht hta w hw hh hbound).trans_lt
    (mul_neg_of_neg_of_pos localExitCoefficient_neg hquart)

lemma localSplitPressure_zero_firstShell (w : TorusL2 12)
    (hw : CriticalSobolev w) (hh : HasOnlyHigherModes w)
    (hbound : ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ)) :
    localSplitPressure 0 w ≤ -localExitD / 2 * criticalEnergy w := by
  have hz : (∫ x, (w x).re ∂torusMeasure 12) = 0 := by
    have h := hw.1
    rw [Legacy.BecknerOnofri.SobolevCentering.fourier_zero] at h
    calc
      _ = (∫ x, w x ∂Legacy.TorusEndpoint.torusMeasure 12).re :=
        integral_re ((Lp.memLp w).integrable (by norm_num))
      _ = 0 := congrArg Complex.re h
  have htilt : firstShellTilt (0 : Fin 12 → ℝ) = fun _ => 1 := by
    have hb : besselI0Two 0 = 1 := by
      rw [besselI0Two_eq_circle_integral]
      simp
    funext x
    simp [firstShellTilt, circleTiltDensity, hb]
  have h := localSplitPressure_preliminary_bound 0 (by simp) (by norm_num) w hw hh hbound
  rw [htilt] at h
  simpa [hz, neg_mul, neg_div] using h

/-- The dimension-twelve exit criterion for actual first-shell and higher Fourier modes. -/
theorem localSplitPressure_lt_zero (t : Fin 12 → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hta : ∀ i, t i ≤ 1 / 14)
    (w : TorusL2 12) (hw : CriticalSobolev w) (hh : HasOnlyHigherModes w)
    (hbound : ∀ᵐ x ∂torusMeasure 12, |(w x).re| ≤ (1 / 30 : ℝ))
    (hne : t ≠ 0 ∨ w ≠ 0) : localSplitPressure t w < 0 := by
  by_cases htne : t = 0
  · subst t
    have hwne : w ≠ 0 := hne.resolve_left (by simp)
    have hnorm : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hwne) 2
    have henergy : 0 < criticalEnergy w := by
      have he := higher_norm_sq_le_energy w hw hh
      linarith
    exact (localSplitPressure_zero_firstShell w hw hh hbound).trans_lt
      (mul_neg_of_neg_of_pos (by linarith [localExitD_pos]) henergy)
  · exact localSplitPressure_lt_zero_of_firstShell_ne t ht hta htne w hw hh hbound

#print axioms localSplitPressure_lt_zero
end BecknerOnofri.HighDim
