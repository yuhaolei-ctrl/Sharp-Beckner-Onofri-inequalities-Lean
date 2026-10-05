import Legacy.BecknerOnofri.SubcriticalAttainmentDefs
import Legacy.BecknerOnofri.ExponentialPartitionContinuity
import Mathlib.Topology.MetricSpace.Lipschitz

/-! The global rough exponential estimate implies quantitative partition
continuity on actual critical Sobolev energy balls. -/
noncomputable section
open Set Filter MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators Topology ENNReal
namespace Legacy.BecknerOnofri.SubcriticalAttainment
open TorusSobolev

theorem rough_integrable {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => Real.exp (p*(u x).re)) (torusMeasure d) := (hR u hu p hp).1

theorem partition_integrable {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) :
    Integrable (fun x => Real.exp (u x).re) (torusMeasure d) := by
  simpa only [one_mul] using rough_integrable hR hu zero_lt_one

theorem partition_pos {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) : 0 < partition u :=
  integral_exp_pos (partition_integrable hR hu)

theorem integral_exp_upper {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) {p : ℝ} (hp : 0 < p) :
    (∫ x, Real.exp (p*(u x).re) ∂torusMeasure d) ≤
      Real.exp (p^2*criticalEnergy u/(4*b)+Real.log Ab) := by
  have hpI := integral_exp_pos (rough_integrable hR hu hp)
  calc
    _ = Real.exp (Real.log (∫ x, Real.exp (p*(u x).re) ∂torusMeasure d)) :=
      (Real.exp_log hpI).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hR u hu p hp).2

theorem integral_exp_two_upper {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) {u : TorusL2 d} (hu : u ∈ realSobolevBall d B) :
    (∫ x, Real.exp (2*(u x).re) ∂torusMeasure d) ≤ Real.exp (B/b+Real.log Ab) := by
  apply (integral_exp_upper hR ⟨hu.2, hu.1.1⟩ (by norm_num : (0:ℝ)<2)).trans
  apply Real.exp_le_exp.mpr
  have hE := div_le_div_of_nonneg_right hu.1.2 hb.le
  have he : (2:ℝ)^2 * criticalEnergy u/(4*b) = criticalEnergy u/b := by field_simp; ring
  rw [he]
  linarith

theorem partition_lipschitzOn_ball {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) :
    LipschitzOnWith ⟨2*Real.sqrt (Real.exp (B/b+Real.log Ab)), by positivity⟩
      (partition (d := d)) (realSobolevBall d B) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro u hu v hv
  have hU := rough_integrable hR ⟨hu.2, hu.1.1⟩ (by norm_num : (0:ℝ)<2)
  have hV := rough_integrable hR ⟨hv.2, hv.1.1⟩ (by norm_num : (0:ℝ)<2)
  have hh := ExponentialPartitionContinuity.partition_difference_bound u v hU hV
  have hU' := Real.sqrt_le_sqrt (integral_exp_two_upper hb hR hu)
  have hV' := Real.sqrt_le_sqrt (integral_exp_two_upper hb hR hv)
  simp only [dist_eq_norm, Real.norm_eq_abs]
  change |partition u-partition v| ≤ (2*Real.sqrt (Real.exp (B/b+Real.log Ab)))*‖u-v‖
  unfold partition
  nlinarith [norm_nonneg (u-v)]

theorem partition_continuousOn_ball {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) :
    ContinuousOn (partition (d := d)) (realSobolevBall d B) :=
  (partition_lipschitzOn_ball hb hR).continuousOn

theorem log_partition_continuousOn_ball {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) :
    ContinuousOn (fun u : TorusL2 d => Real.log (partition u)) (realSobolevBall d B) := by
  apply (partition_continuousOn_ball hb hR).log
  intro u hu
  exact (partition_pos hR ⟨hu.2, hu.1.1⟩).ne'

theorem coercivity {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    (A : ℝ) {u : TorusL2 d} (hu : Admissible u) :
    functional A u ≤ Real.log Ab - (A-1/(4*b))*criticalEnergy u := by
  have hh := (hR u hu 1 zero_lt_one).2
  simp only [one_mul, one_pow] at hh
  unfold functional partition
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

/-- Bounded-energy L² convergence entails convergence of actual partition integrals. -/
theorem partition_tendsto_of_bounded_energy {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) {u : ℕ → TorusL2 d} {v : TorusL2 d}
    (hu : ∀ n, u n ∈ realSobolevBall d B) (hv : v ∈ realSobolevBall d B)
    (hl : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => partition (u n)) atTop (𝓝 (partition v)) :=
  ((partition_continuousOn_ball hb hR) v hv).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hl, Filter.Eventually.of_forall hu⟩)

#print axioms partition_lipschitzOn_ball
#print axioms partition_tendsto_of_bounded_energy
#print axioms coercivity

end Legacy.BecknerOnofri.SubcriticalAttainment
