import Legacy.BecknerOnofri.EndpointPotential

/-! Heat-density concentration gives actual admissible potential counterexamples
to every coefficient below the endpoint potential coefficient. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.EndpointPotential
open TorusSobolev SubcriticalAttainment SubcriticalEuler SubcriticalPrimalDual

theorem density_sharpness_L2 {d : ℕ} (hd : 0 < d) {C : ℝ} (hC : endpointConstant d < C) :
    ∃ r : ProbabilityDensity d, MemLp r.value 2 (torusMeasure d) ∧ r.FiniteEntropy ∧
      densityEntropy r.value < C*fourierEnergy r := by
  have hsigma := endpointSigma_pos hd
  have hC' : (d:ℝ) < C*endpointSigma d := (div_lt_iff₀ hsigma).mp hC
  obtain ⟨t,ht,_,hfail⟩ := EndpointSharpness.exists_heatDensity_violation hd hC'
  let r := EndpointSharpnessHeat.heatDensity d ht
  have hr : MemLp r.value 2 (torusMeasure d) := EndpointSharpnessHeat.heatDensity_memLp d ht
  obtain ⟨_,heq⟩ := PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd r hr
  refine ⟨r,hr,EndpointSharpnessHeat.heatDensity_finiteEntropy d ht,?_⟩
  change densityEntropy r.value < (C*endpointSigma d)*PhysicalGreenL2.physicalGreenEnergy r at hfail
  rw [heq,normalized_energy] at hfail
  convert hfail using 1
  field_simp

/-- Sharpness has concrete actual Sobolev witnesses, not merely a necessary
inequality between symbolic coefficients. -/
theorem potential_sharpness {d : ℕ} (hd : 0 < d) (hE : Endpoint d) {a : ℝ}
    (ha : a < coefficient d) :
    ∃ u : TorusL2 d, Admissible u ∧ Integrable (fun x => Real.exp (u x).re) (torusMeasure d) ∧
      a*criticalEnergy u < Real.log (partition u) := by
  obtain ⟨A,hAlo,hAhi⟩ := exists_between (max_lt ha (coefficient_pos hd))
  have hA : 0 < A := (le_max_right a 0).trans_lt hAlo
  have hAa : a < A := (le_max_left a 0).trans_lt hAlo
  have hCpos := endpointConstant_pos hd
  have hC : endpointConstant d < 1/(4*A) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4*A)).mpr
    have h := (lt_div_iff₀ (by positivity : 0 < 4*endpointConstant d)).mp hAhi
    nlinarith
  obtain ⟨r,hr,_,hfail⟩ := density_sharpness_L2 hd hC
  let u := dualPotential A r hr
  have hu := dualPotential_admissible hd A r hr
  have hdual := density_le_dual hd (rough_of_endpoint hd hE) hA r hr
  change densityFunctional A r ≤ functional A u at hdual
  have hf : 0 < functional A u := lt_of_lt_of_le (sub_pos.mpr hfail) hdual
  refine ⟨u,hu,(onofri hd hE hu).1,?_⟩
  have hmono := mul_le_mul_of_nonneg_right hAa.le (energy_nonneg u)
  unfold functional at hf
  linarith

theorem coefficient_le_of_potential_bound {d : ℕ} (hd : 0 < d) (hE : Endpoint d) (a : ℝ)
    (hbound : ∀ u : TorusL2 d, Admissible u → Real.log (partition u) ≤ a*criticalEnergy u) :
    coefficient d ≤ a := by
  by_contra h
  obtain ⟨u,hu,_,hf⟩ := potential_sharpness hd hE (lt_of_not_ge h)
  exact (not_lt_of_ge (hbound u hu)) hf

theorem coefficient_isLeast {d : ℕ} (hd : 0 < d) (hE : Endpoint d) :
    IsLeast {a : ℝ | ∀ u : TorusL2 d, Admissible u →
      Real.log (partition u) ≤ a*criticalEnergy u} (coefficient d) :=
  ⟨fun _ hu => (onofri hd hE hu).2,fun a ha => coefficient_le_of_potential_bound hd hE a ha⟩

#print axioms potential_sharpness
#print axioms coefficient_isLeast
end Legacy.BecknerOnofri.EndpointPotential
