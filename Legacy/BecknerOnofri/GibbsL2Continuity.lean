module

public import Legacy.BecknerOnofri.ExponentialL2Continuity
public import Legacy.BecknerOnofri.SubcriticalGibbs

@[expose] public section

/-! The actual Gibbs map is continuous from bounded critical Sobolev energy
balls with their L2 topology into real L2 densities. -/
noncomputable section
namespace Legacy.BecknerOnofri.GibbsL2Continuity
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open ExponentialPartitionContinuity ExponentialL2Continuity

abbrev EnergyBall (d : ℕ) (B : ℝ) := ↥(realSobolevBall d B)
abbrev DensityL2 (d : ℕ) := Lp ℝ 2 (torusMeasure d)

theorem ball_admissible {d : ℕ} {B : ℝ} (u : EnergyBall d B) : Admissible u.1 :=
  ⟨u.2.2, u.2.1.1⟩

def expLp {d : ℕ} {b Ab B : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : EnergyBall d B) : DensityL2 d :=
  (exp_memLp_two u.1 (rough_integrable hR (ball_admissible u) (by norm_num : (0:ℝ)<2))).toLp _

theorem expLp_ae {d : ℕ} {b Ab B : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : EnergyBall d B) : expLp hR u =ᵐ[torusMeasure d] (fun x => Real.exp (u.1 x).re) :=
  (exp_memLp_two u.1 (rough_integrable hR (ball_admissible u) (by norm_num : (0:ℝ)<2))).coeFn_toLp

theorem integral_exp_four_upper {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) (u : EnergyBall d B) :
    (∫ x, Real.exp (4*(u.1 x).re) ∂torusMeasure d) ≤ Real.exp (4*B/b+Real.log Ab) := by
  apply (integral_exp_upper hR (ball_admissible u) (by norm_num : (0:ℝ)<4)).trans
  apply Real.exp_le_exp.mpr
  have hE := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right u.2.1.2 hb.le)
    (by norm_num : (0:ℝ) ≤ 4)
  have he : (4:ℝ)^2*criticalEnergy u.1/(4*b) = 4*(criticalEnergy u.1/b) := by field_simp
  rw [he]
  rw [mul_div_assoc]
  linarith only [hE]

theorem norm_expLp_sub_sq_le {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) (u v : EnergyBall d B) :
    ‖expLp hR u-expLp hR v‖^2 ≤
      (4*Real.sqrt (Real.exp (4*B/b+Real.log Ab)))*dist u v := by
  unfold expLp
  rw [norm_sub_toLp_sq]
  have h := squared_difference_bound u.1 v.1
    (rough_integrable hR (ball_admissible u) (by norm_num : (0:ℝ)<2))
    (rough_integrable hR (ball_admissible v) (by norm_num : (0:ℝ)<2))
    (rough_integrable hR (ball_admissible u) (by norm_num : (0:ℝ)<4))
    (rough_integrable hR (ball_admissible v) (by norm_num : (0:ℝ)<4))
  have hU := Real.sqrt_le_sqrt (integral_exp_four_upper hb hR u)
  have hV := Real.sqrt_le_sqrt (integral_exp_four_upper hb hR v)
  rw [Subtype.dist_eq, dist_eq_norm]
  nlinarith [norm_nonneg (u.1-v.1)]

theorem expLp_continuous {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) : Continuous (expLp hR : EnergyBall d B → DensityL2 d) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  rw [Metric.continuousAt_iff]
  intro ε hε
  let C : ℝ := 4*Real.sqrt (Real.exp (4*B/b+Real.log Ab))
  have hC : 0 ≤ C := by positivity
  refine ⟨ε^2/(C+1), div_pos (sq_pos_of_pos hε) (by linarith), ?_⟩
  intro v hv
  have hv' := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hv
  have h := norm_expLp_sub_sq_le hb hR v u
  change ‖expLp hR v-expLp hR u‖^2 ≤ C*dist v u at h
  rw [dist_eq_norm]
  nlinarith [dist_nonneg (x := v) (y := u), norm_nonneg (expLp hR v-expLp hR u)]

def gibbsLp {d : ℕ} {b Ab B : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : EnergyBall d B) : DensityL2 d := (partition u.1)⁻¹ • expLp hR u

theorem gibbsLp_continuous {d : ℕ} {b Ab B : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) : Continuous (gibbsLp hR : EnergyBall d B → DensityL2 d) := by
  have hp : Continuous (fun u : EnergyBall d B => partition u.1) :=
    continuousOn_iff_continuous_restrict.mp (partition_continuousOn_ball hb hR)
  exact (hp.inv₀ (fun u => (partition_pos hR (ball_admissible u)).ne')).smul (expLp_continuous hb hR)

theorem gibbsLp_ae {d : ℕ} {b Ab B : ℝ} (hR : RoughExponentialBound d b Ab)
    (u : EnergyBall d B) : gibbsLp hR u =ᵐ[torusMeasure d] gibbsValue u.1 := by
  filter_upwards [Lp.coeFn_smul (partition u.1)⁻¹ (expLp hR u), expLp_ae hR u] with x hx he
  change (((partition u.1)⁻¹ • expLp hR u) x) = _
  rw [hx]
  change (partition u.1)⁻¹ * expLp hR u x = _
  rw [he]
  simp [gibbsValue, div_eq_mul_inv, mul_comm]

theorem gibbsLp_range_isCompact {d : ℕ} (hd : 0 < d) {b Ab B : ℝ} (hb : 0 < b)
    (hB : 0 ≤ B) (hR : RoughExponentialBound d b Ab) :
    IsCompact (Set.range (gibbsLp hR : EnergyBall d B → DensityL2 d)) := by
  letI : CompactSpace (EnergyBall d B) := isCompact_iff_compactSpace.mp (realSobolevBall_isCompact hd hB)
  exact isCompact_range (gibbsLp_continuous hb hR)

#print axioms gibbsLp_continuous
#print axioms gibbsLp_range_isCompact
end Legacy.BecknerOnofri.GibbsL2Continuity
