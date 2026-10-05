module

public import Legacy.BecknerOnofri.LowDimensionThresholds
public import Legacy.BecknerOnofri.LowDimensionPhysicalEndpoint

@[expose] public section

/-! Explicit heat-density concentration makes the pressure infinite above
collapse and the coefficient defect infinite below the sharp threshold. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped ENNReal
namespace Legacy.BecknerOnofri.CollapseDivergence
open EndpointSharpness EndpointSharpnessHeat PhysicalGreenL2 TorusHeatPositivity
open TorusSobolev SubcriticalAttainment SubcriticalPrimalDual EndpointPotential
open LowDimensionThresholds

/-- Arbitrarily large physical interaction deficits have actual smooth heat
density witnesses. This strengthens concentration sharpness quantitatively. -/
theorem heat_gap_unbounded {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : (d:ℝ) < C) (M : ℝ) :
    ∃ (t : ℝ) (ht : 0 < t), t ≤ 1 ∧
      M < C*physicalGreenEnergy (heatDensity d ht)-densityEntropy (heatDensity d ht).value := by
  let P : ℝ := (d:ℝ)*Real.log (theta 1 0).re
  let B : ℝ := (d:ℝ)/2+1/(d:ℝ)
  have hdR : (0:ℝ) < (d:ℝ) := Nat.cast_pos.mpr hd
  have hCp : 0 < C := hdR.trans hC
  have hP : 0 ≤ P := mul_nonneg (Nat.cast_nonneg d)
    (Real.log_nonneg (theta_zero_one_le (by norm_num : (0:ℝ)<1)))
  have hB : 0 < B := by dsimp [B]; positivity
  let L : ℝ := 2*(P+C*B+max M 0+1)/(C-(d:ℝ))
  have hLp : 0 < L := by dsimp [L]; positivity
  have hLeq : (C-(d:ℝ))*L = 2*(P+C*B+max M 0+1) := by
    dsimp [L]
    field_simp [(sub_pos.mpr hC).ne']
  let t : ℝ := Real.exp (-L)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hlog : Real.log t = -L := Real.log_exp _
  refine ⟨t, ht, ht1, ?_⟩
  have hEnt := heatDensity_entropy_log_bound (d := d) ht ht1
  have hEnergy := heatDensity_energy_log_lower hd ht ht1
  rw [hlog] at hEnt hEnergy
  have hEnt' : densityEntropy (heatDensity d ht).value ≤ (d:ℝ)/2*L+P := by
    dsimp only [P]
    nlinarith only [hEnt]
  have hEnergy' : L/2-B ≤ physicalGreenEnergy (heatDensity d ht) := by
    dsimp only [B]
    nlinarith only [hEnergy]
  have hh := mul_le_mul_of_nonneg_left hEnergy' hCp.le
  nlinarith only [hh, hEnt', hLeq, le_max_left M 0]

theorem pressure_above_collapse {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 2*(d:ℝ) < β) :
    pressure d β = ∞ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro R
  obtain ⟨t, ht, _, hgap⟩ := heat_gap_unbounded hd (by linarith : (d:ℝ)<β/2) (R:ℝ)
  have hr := heatDensity_finiteEntropy d ht
  rw [(heatDensity_spectral_finite_and_physical hd ht).2] at hgap
  have hle : (R:ℝ≥0∞) ≤ ENNReal.ofReal ((β/2)*densitySpectralEnergy (heatDensity d ht)-
      densityEntropy (heatDensity d ht).value) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hgap.le
  exact hle.trans (le_iSup_of_le (heatDensity d ht) (le_iSup_of_le hr le_rfl))

theorem potential_gap_unbounded {d : ℕ} (hd : 0 < d) (hE : Endpoint d) {a : ℝ}
    (ha : a < coefficient d) (M : ℝ) :
    ∃ u : TorusL2 d, Admissible u ∧ M < Real.log (partition u)-a*criticalEnergy u := by
  obtain ⟨A, hAlo, hAhi⟩ := exists_between (max_lt ha (coefficient_pos hd))
  have hA : 0 < A := (le_max_right a 0).trans_lt hAlo
  have hAa : a < A := (le_max_left a 0).trans_lt hAlo
  have hCpos := EndpointPotential.endpointConstant_pos hd
  have hC : endpointConstant d < 1/(4*A) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4*A)).mpr
    have h := (lt_div_iff₀ (by positivity : 0 < 4*endpointConstant d)).mp hAhi
    nlinarith
  have hσ := endpointSigma_pos hd
  have hphysical : (d:ℝ) < endpointSigma d/(4*A) := by
    change (d:ℝ)/endpointSigma d < 1/(4*A) at hC
    have hh := (div_lt_iff₀ hσ).mp hC
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh
  obtain ⟨t, ht, _, hgap⟩ := heat_gap_unbounded hd hphysical M
  let r := heatDensity d ht
  have hr : MemLp r.value 2 (torusMeasure d) := heatDensity_memLp d ht
  let u := dualPotential A r hr
  have hu := dualPotential_admissible hd A r hr
  have hdual := density_le_dual hd (rough_of_endpoint hd hE) hA r hr
  have hQ := (physicalGreenEnergy_eq_spectral hd r hr).2
  change M < endpointSigma d/(4*A)*physicalGreenEnergy r-densityEntropy r.value at hgap
  rw [hQ, normalized_energy] at hgap
  have hcoef : endpointSigma d/(4*A)*(fourierEnergy r/endpointSigma d) =
      (1/(4*A))*fourierEnergy r := by field_simp
  rw [hcoef] at hgap
  change M < densityFunctional A r at hgap
  have hJ : M < functional A u := hgap.trans_le hdual
  refine ⟨u, hu, ?_⟩
  unfold functional at hJ
  have hmono := mul_le_mul_of_nonneg_right hAa.le (energy_nonneg u)
  linarith

theorem coefficientDefect_below_collapse {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) {A : ℝ}
    (hA : A < 1/(4*(d:ℝ)*endpointSymbolConstant d)) : coefficientDefect d A = ∞ := by
  have hd0 : 0 < d := by omega
  have hscale : coefficient d = (1/(4*(d:ℝ)*endpointSymbolConstant d))*(2*Real.pi)^d := by
    rw [← endpointSymbolConstant_mul_sigma hd0]
    unfold coefficient endpointConstant
    field_simp [(endpointSymbolConstant_pos hd0).ne']
  have hsmall : A*(2*Real.pi)^d < coefficient d := by
    rw [hscale]
    exact mul_lt_mul_of_pos_right hA (pow_pos (by positivity) _)
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro R
  obtain ⟨u, hu, hgap⟩ := potential_gap_unbounded hd0 (endpoint_through_ten d hd hd10) hsmall (R:ℝ)
  have he : Real.log (centeredPartition u)-A*manuscriptEnergy u =
      Real.log (partition u)-(A*(2*Real.pi)^d)*criticalEnergy u := by
    rw [centeredPartition_admissible hu, manuscriptEnergy_eq hd0 u hu.2.2]
    ring
  rw [← he] at hgap
  have hle : (R:ℝ≥0∞) ≤ ENNReal.ofReal (Real.log (centeredPartition u)-A*manuscriptEnergy u) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hgap.le
  exact hle.trans (le_iSup_of_le u (le_iSup_of_le hu.1 (le_iSup_of_le hu.2.2 le_rfl)))

#print axioms heat_gap_unbounded
#print axioms pressure_above_collapse
#print axioms coefficientDefect_below_collapse

theorem pressure_formula {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2*(d:ℝ) then 0 else ∞ := by
  by_cases hβ : β ≤ 2*(d:ℝ)
  · rw [if_pos hβ]
    exact (pressure_zero_iff hd hd10 β).mpr hβ
  · rw [if_neg hβ]
    exact pressure_above_collapse (by omega) (lt_of_not_ge hβ)

theorem coefficientDefect_formula {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A =
      if 1/(4*(d:ℝ)*endpointSymbolConstant d) ≤ A then 0 else ∞ := by
  by_cases hA : 1/(4*(d:ℝ)*endpointSymbolConstant d) ≤ A
  · rw [if_pos hA]
    exact (coefficientDefect_zero_iff hd hd10 A).mpr hA
  · rw [if_neg hA]
    exact coefficientDefect_below_collapse hd hd10 (lt_of_not_ge hA)

#print axioms pressure_formula
#print axioms coefficientDefect_formula
end Legacy.BecknerOnofri.CollapseDivergence
