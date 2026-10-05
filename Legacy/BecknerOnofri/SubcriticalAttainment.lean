module

public import Legacy.BecknerOnofri.SubcriticalExponentialBounds

@[expose] public section

/-! A genuine subcritical global maximizer follows from the full-function
rough exponential estimate. No optimizer or convergence is assumed. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal
namespace Legacy.BecknerOnofri.SubcriticalAttainment
open TorusSobolev

theorem rough_log_nonneg {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab) :
    0 ≤ Real.log Ab := by
  have hh := coercivity hR 0 (admissible_zero d)
  simpa using hh

theorem functional_upperSemicontinuousOn_ball {d : ℕ} {b Ab A B : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) (hR : RoughExponentialBound d b Ab) :
    UpperSemicontinuousOn (functional A : TorusL2 d → ℝ) (realSobolevBall d B) := by
  have henergy := (show Continuous (fun t : ℝ => -(A*t)) by fun_prop).comp_lowerSemicontinuousOn_antitone
    (energy_lowerSemicontinuousOn d B)
    (fun x y hxy => neg_le_neg (mul_le_mul_of_nonneg_left hxy hA))
  have hlog := (log_partition_continuousOn_ball hb hR (B := B)).upperSemicontinuousOn
  unfold functional
  simpa only [sub_eq_add_neg, Function.comp_def] using hlog.add henergy

theorem zero_mem_realSobolevBall {d : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    (0 : TorusL2 d) ∈ realSobolevBall d B := by
  exact ⟨⟨criticalSobolev_zero d, by simpa using hB⟩, realPotential_zero d⟩

/-- Compactness and upper semicontinuity produce an actual maximizer on every energy ball. -/
theorem exists_maximizer_on_ball {d : ℕ} (hd : 0 < d) {b Ab A B : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : RoughExponentialBound d b Ab) :
    ∃ u : TorusL2 d, u ∈ realSobolevBall d B ∧
      ∀ v ∈ realSobolevBall d B, functional A v ≤ functional A u := by
  obtain ⟨u, hu, hmax⟩ := (functional_upperSemicontinuousOn_ball hb hA hR (B := B)).exists_isMaxOn
    ⟨0, zero_mem_realSobolevBall hB⟩ (realSobolevBall_isCompact hd hB)
  exact ⟨u, hu, hmax⟩

/-- Subcritical coercivity excludes the exterior of one explicitly bounded energy ball. -/
theorem exists_global_maximizer {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hb : 0 < b) (hA : 1/(4*b) < A) (hR : RoughExponentialBound d b Ab) :
    ∃ u : TorusL2 d, Admissible u ∧
      criticalEnergy u ≤ (Real.log Ab+1)/(A-1/(4*b)) ∧
      0 ≤ functional A u ∧ ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u := by
  let B : ℝ := (Real.log Ab+1)/(A-1/(4*b))
  have hdelta : 0 < A-1/(4*b) := sub_pos.mpr hA
  have hlog := rough_log_nonneg hR
  have hB : 0 ≤ B := div_nonneg (by linarith) hdelta.le
  have hA0 : 0 ≤ A := by
    have : 0 < 1/(4*b) := by positivity
    linarith
  obtain ⟨u, hu, hmax⟩ := exists_maximizer_on_ball hd hb hA0 hB hR
  have hzero : 0 ≤ functional A u := by
    simpa using hmax 0 (zero_mem_realSobolevBall hB)
  refine ⟨u, ⟨hu.2, hu.1.1⟩, hu.1.2, hzero, ?_⟩
  intro v hv
  by_cases hvB : criticalEnergy v ≤ B
  · exact hmax v ⟨⟨hv.2, hvB⟩, hv.1⟩
  · have hlarge : B < criticalEnergy v := lt_of_not_ge hvB
    have hmul : Real.log Ab+1 < (A-1/(4*b))*criticalEnergy v := by
      have hh := (div_lt_iff₀ hdelta).mp hlarge
      nlinarith
    have hcoer := coercivity hR A hv
    linarith

#print axioms exists_maximizer_on_ball
#print axioms exists_global_maximizer
end Legacy.BecknerOnofri.SubcriticalAttainment
