import Legacy.TorusEndpoint.EndpointSharpnessHeat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative concentration sharpness for the actual Green kernel

The endpoint inequality itself is not a premise. This module studies the
positive continuous heat densities constructed in `EndpointSharpnessHeat`.
-/

open MeasureTheory Filter Set
open scoped Topology Interval

namespace Legacy.TorusEndpoint.EndpointSharpness

open EndpointSharpnessHeat PhysicalGreenL2 TorusHeatPositivity

theorem rpow_neg_two (u : ℝ) : u ^ (-2 : ℝ) = (u ^ (2 : ℕ))⁻¹ := by
  simp only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]

noncomputable def heatEnergyLowerIntegrand (d : ℕ) (t u : ℝ) : ℝ :=
  u⁻¹ - ((d : ℝ) * t) * (u ^ 2)⁻¹ - u ^ ((d : ℝ) / 2 - 1)

theorem heatEnergyLowerIntegrand_intervalIntegrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (heatEnergyLowerIntegrand d t) volume t 1 := by
  have hz : (0 : ℝ) ∉ [[t, 1]] := notMem_uIcc_of_lt ht (by norm_num)
  have hr (a : ℝ) : IntervalIntegrable (fun u : ℝ => u ^ a) volume t 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hi : IntervalIntegrable (fun u : ℝ => u⁻¹) volume t 1 := by
    simpa only [Real.rpow_neg_one] using hr (-1)
  have hi2 : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹) volume t 1 := by
    simpa only [rpow_neg_two] using hr (-2)
  exact (hi.sub (hi2.const_mul _)).sub (hr _)

theorem heatEnergyLowerIntegrand_integral {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    (∫ u in t..1, heatEnergyLowerIntegrand d t u) =
      -Real.log t - (d : ℝ) * (1 - t) -
        (1 - t ^ ((d : ℝ) / 2)) / ((d : ℝ) / 2) := by
  have hz : (0 : ℝ) ∉ [[t, 1]] := notMem_uIcc_of_lt ht (by norm_num)
  have hr (a : ℝ) : IntervalIntegrable (fun u : ℝ => u ^ a) volume t 1 :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hz)
  have hi : IntervalIntegrable (fun u : ℝ => u⁻¹) volume t 1 := by
    simpa only [Real.rpow_neg_one] using hr (-1)
  have hi2 : IntervalIntegrable (fun u : ℝ => (u ^ 2)⁻¹) volume t 1 := by
    simpa only [rpow_neg_two] using hr (-2)
  have he2 : (∫ u in t..1, (u ^ 2)⁻¹) = t⁻¹ - 1 := by
    simp_rw [← rpow_neg_two]
    rw [integral_rpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num [Real.rpow_neg_one]
    ring
  have ha : 0 < (d : ℝ) / 2 := by positivity
  have hea : (∫ u in t..1, u ^ ((d : ℝ) / 2 - 1)) =
      (1 - t ^ ((d : ℝ) / 2)) / ((d : ℝ) / 2) := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp only [sub_add_cancel, Real.one_rpow]
  unfold heatEnergyLowerIntegrand
  rw [intervalIntegral.integral_sub (hi.sub (hi2.const_mul _)) (hr _),
    intervalIntegral.integral_sub hi (hi2.const_mul _),
    intervalIntegral.integral_const_mul, he2, hea,
    integral_inv_of_pos ht (by norm_num), Real.log_div one_ne_zero ht.ne',
    Real.log_one, zero_sub]
  field_simp

/-- Explicit lower logarithmic growth with a finite dimension-dependent error. -/
theorem heatDensity_energy_log_lower {d : ℕ} (hd : 0 < d) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    -(1 / 2 : ℝ) * Real.log t - (d : ℝ) / 2 - 1 / (d : ℝ) ≤
      physicalGreenEnergy (heatDensity d ht) := by
  have hsub : Ioc t 1 ⊆ Ioi (0 : ℝ) := fun u hu => ht.trans hu.1
  have hi := heatEnergyIntegrand_integrable hd ht
  have hiI : IntervalIntegrable (heatEnergyIntegrand d t) volume t 1 := by
    rw [intervalIntegrable_iff, uIoc_of_le ht1]
    exact hi.mono_set hsub
  have hmono := intervalIntegral.integral_mono_on ht1
    (heatEnergyLowerIntegrand_intervalIntegrable (d := d) ht) hiI
    (fun u hu => heatEnergyIntegrand_lower (d := d) ht (ht.trans_le hu.1))
  have hpos : 0 ≤ᵐ[volume.restrict (Ioi 0)] heatEnergyIntegrand d t := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact heatEnergyIntegrand_nonneg ht hu
  have hfull := setIntegral_mono_set hi hpos hsub.eventuallyLE
  rw [← intervalIntegral.integral_of_le ht1, heatDensity_energy_mellin hd ht] at hfull
  have hbound := hmono.trans hfull
  rw [heatEnergyLowerIntegrand_integral hd ht] at hbound
  have hdp : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hpow : 0 ≤ t ^ ((d : ℝ) / 2) := Real.rpow_nonneg ht.le _
  have hfrac : (1 - t ^ ((d : ℝ) / 2)) / ((d : ℝ) / 2) ≤ 2 / (d : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) / 2)).mpr
    field_simp
    nlinarith
  have hdt : 0 ≤ (d : ℝ) * t := by positivity
  simp only [div_eq_mul_inv] at hbound hfrac ⊢
  nlinarith

/-- Every coefficient strictly larger than d fails already on an explicit
positive continuous heat probability density. No endpoint cap is assumed. -/
theorem exists_heatDensity_violation {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : (d : ℝ) < C) :
    ∃ (t : ℝ) (ht : 0 < t), t ≤ 1 ∧
      densityEntropy (heatDensity d ht).value < C * physicalGreenEnergy (heatDensity d ht) := by
  let A : ℝ := (d : ℝ) * Real.log (theta 1 0).re
  let B : ℝ := (d : ℝ) / 2 + 1 / (d : ℝ)
  have hdp : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hCp : 0 < C := hdp.trans hC
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg d)
    (Real.log_nonneg (theta_zero_one_le (by norm_num : (0 : ℝ) < 1)))
  have hB : 0 < B := by dsimp [B]; positivity
  let L : ℝ := 2 * (A + C * B + 1) / (C - (d : ℝ))
  have hLp : 0 < L := by dsimp [L]; positivity
  have hLeq : (C - (d : ℝ)) * L = 2 * (A + C * B + 1) := by
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
  have hEnt' : densityEntropy (heatDensity d ht).value ≤ (d : ℝ) / 2 * L + A := by
    dsimp only [A]
    nlinarith [hEnt]
  have hEnergy' : L / 2 - B ≤ physicalGreenEnergy (heatDensity d ht) := by
    dsimp only [B]
    nlinarith [hEnergy]
  have hGap : (d : ℝ) / 2 * L + A < C * (L / 2 - B) := by nlinarith [hLeq]
  exact (hEnt'.trans_lt hGap).trans_le (mul_le_mul_of_nonneg_left hEnergy' hCp.le)

/-- The witnesses have actual finite entropy and an integrable actual physical
interaction; the conclusion is not about a formal or totalized divergent sum. -/
theorem exists_finiteEntropy_violation {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : (d : ℝ) < C) :
    ∃ rho : ProbabilityDensity d,
      Continuous rho.value ∧ (∀ x, 0 < rho.value x) ∧ rho.FiniteEntropy ∧
      Integrable (fun xy : Torus d × Torus d =>
        GreenKernelReal.realGreen d (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
        ((torusMeasure d).prod (torusMeasure d)) ∧
      densityEntropy rho.value < C * physicalGreenEnergy rho := by
  obtain ⟨t, ht, _, hfail⟩ := exists_heatDensity_violation hd hC
  exact ⟨heatDensity d ht, heatDensity_continuous d ht, heatDensity_pos d ht,
    heatDensity_finiteEntropy d ht, realGreen_interaction_integrable _ (heatDensity_memLp d ht),
    hfail⟩

/-- Necessary upper bound on any universally valid coefficient. This theorem
does not assert validity of the endpoint coefficient itself. -/
theorem coefficient_le_dimension_of_uniform_bound {d : ℕ} (hd : 0 < d) (C : ℝ)
    (hbound : ∀ rho : ProbabilityDensity d, rho.FiniteEntropy →
      C * physicalGreenEnergy rho ≤ densityEntropy rho.value) : C ≤ (d : ℝ) := by
  by_contra h
  obtain ⟨rho, _, _, hEnt, _, hfail⟩ := exists_finiteEntropy_violation hd (lt_of_not_ge h)
  exact (not_lt_of_ge (hbound rho hEnt)) hfail

end Legacy.TorusEndpoint.EndpointSharpness
