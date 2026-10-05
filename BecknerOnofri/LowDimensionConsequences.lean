import BecknerOnofri.LowDimensionRaw
import BecknerOnofri.RawAttainment
import BecknerOnofri.PressureRegularity
import BecknerOnofri.ThresholdReduction
import BecknerOnofri.PressureDuality

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate
namespace BecknerOnofri.HighDim.LowDimension

theorem physical_density_bound {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Integrable (fun z : Torus d × Torus d =>
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d (z.1-z.2) * ρ.value z.1 * ρ.value z.2)
        ((torusMeasure d).prod (torusMeasure d)) ∧
    (d : ℝ) * (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x-y) *
      ρ.value x * ρ.value y ∂torusMeasure d ∂torusMeasure d) ≤ entropy ρ :=
  Legacy.BecknerOnofri.physical_green_endpoint hd hd10 (Bridge.density ρ) hρ

theorem circle_potential (u : Torus 1 → ℝ) (hu : InCriticalSobolev u) :
    (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
        u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1-conj a*fourier 1 (x 0)‖+c) := by
  have h := Legacy.BecknerOnofri.CircleEquality.onofri_equality_iff_paper_family
    (Bridge.potentialLp_real u hu.1) (Bridge.potentialLp_summable (by norm_num) u hu)
  rw [partition_eq, manuscriptEnergy_eq (by norm_num) u hu] at h
  have hc := coefficient_eq (by norm_num : 0 < 1)
  norm_num only [Nat.cast_one, mul_one] at hc h
  rw [← hc] at h
  rw [logPartition_eq_log_integral (by norm_num) u hu, EReal.coe_eq_coe_iff, h]
  constructor
  · rintro ⟨a, ha, c, hc⟩
    refine ⟨a, ha, c, ?_⟩
    filter_upwards [hc, Bridge.potentialLp_ae u hu.1] with x hx hu'
    have := congrArg Complex.re (hu'.symm.trans hx)
    simpa using this
  · rintro ⟨a, ha, c, hc⟩
    refine ⟨a, ha, c, ?_⟩
    filter_upwards [hc, Bridge.potentialLp_ae u hu.1] with x hx hu'
    simpa [hx] using hu'

theorem circle_density (ρ : ProbabilityDensity 1) (hρ : ρ.FiniteEntropy) :
    ((((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
        (entropy ρ : EReal) ↔
      ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
        fun x => (1-‖a‖^2)/‖fourier 1 (x 0)-a‖^2) := by
  have h := Legacy.BecknerOnofri.CircleEquality.density_equality_iff_paper_family
    (Bridge.density ρ) hρ
  rw [fourierEnergy_eq] at h
  unfold Legacy.BecknerOnofri.endpointConstant at h
  norm_num only [Nat.cast_one] at h
  change ((1 : ℝ) / spectralThreshold 1 * (∑' k, spectralTerm ρ k) = entropy ρ ↔ _) at h
  rw [spectralEnergy_coe_eq_tsum (by norm_num) ρ hρ]
  exact_mod_cast h

theorem collapse_normalization {d : ℕ} (hd : 0 < d) :
    collapseCoefficient d * (2 * Real.pi)^d = Legacy.BecknerOnofri.EndpointPotential.coefficient d := by
  unfold collapseCoefficient Legacy.BecknerOnofri.EndpointPotential.coefficient
    Legacy.BecknerOnofri.endpointConstant
  rw [← Bridge.spectralThreshold_eq]
  have hs := Legacy.TorusEndpoint.endpointSigma_pos hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  field_simp

theorem coefficient_above_zero {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    {A : ℝ} (hA : collapseCoefficient d ≤ A) : coefficientDefect d A = 0 := by
  apply le_antisymm ?_ (coefficientDefect_nonneg _ _)
  unfold coefficientDefect
  refine iSup_le fun u => iSup_le fun hu => ?_
  have hb := (potential_bound hd hd10 u hu).2
  rw [logPartition_eq_log_integral (by omega) u hu] at hb ⊢
  have hE : 0 ≤ potentialEnergy u := by
    apply tsum_nonneg
    intro k
    unfold potentialTerm frequencyLength
    positivity
  have hR : Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤
      collapseCoefficient d * potentialEnergy u := by exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_right hA hE
  exact_mod_cast (show Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) -
    A * potentialEnergy u ≤ 0 by linarith)

theorem coefficient_below_infinite {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10)
    {A : ℝ} (hA : A < collapseCoefficient d) : coefficientDefect d A = ⊤ := by
  have hsmall : A * (2 * Real.pi)^d < Legacy.BecknerOnofri.EndpointPotential.coefficient d := by
    rw [← collapse_normalization (by omega)]
    exact mul_lt_mul_of_pos_right hA (by positivity)
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  obtain ⟨u, hu, hgap⟩ := Legacy.BecknerOnofri.CollapseDivergence.potential_gap_unbounded
    (by omega) (Legacy.BecknerOnofri.endpoint_through_ten d hd hd10) hsmall M
  have hg : (M : EReal) < RawAttainment.rawFunctional A (RawAttainment.realValue u) := by
    rw [RawAttainment.rawFunctional_realValue (by omega) A u hu]
    exact_mod_cast hgap
  exact hg.trans_le (le_iSup_of_le (RawAttainment.realValue u)
    (le_iSup_of_le (RawAttainment.realValue_sobolev u hu) le_rfl))

theorem coefficient_formula {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (A : ℝ) :
    coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤ := by
  split_ifs with hA
  · exact coefficient_above_zero hd hd10 hA
  · exact coefficient_below_infinite hd hd10 (lt_of_not_ge hA)

theorem potential_coefficient_sharp {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) := by
  refine ⟨fun u hu => (potential_bound hd hd10 u hu).2, ?_⟩
  intro A hA
  by_contra hh
  have hinf := coefficient_below_infinite hd hd10 (lt_of_not_ge hh)
  have hzero : coefficientDefect d A ≤ 0 := by
    unfold coefficientDefect
    refine iSup_le fun u => iSup_le fun hu => ?_
    have h := hA u hu
    rw [logPartition_eq_log_integral (by omega) u hu] at h ⊢
    have hr : Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A * potentialEnergy u := by
      exact_mod_cast h
    exact_mod_cast sub_nonpos.mpr hr
  simpa [hinf] using hzero

theorem pressure_formula {d : ℕ} (hd : 1 ≤ d) (hd10 : d ≤ 10) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ := by
  have hs := Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0 < d)
  change 0 < spectralThreshold d at hs
  split_ifs with hβ
  · apply le_antisymm ?_ (pressure_nonneg _ _)
    unfold pressure
    refine iSup_le fun ρ => iSup_le fun hρ => ?_
    have hbound := density_bound hd hd10 ρ hρ
    rw [spectralEnergy_coe_eq_tsum (by omega) ρ hρ] at hbound ⊢
    have hb : (d : ℝ) / spectralThreshold d * (∑' k, spectralTerm ρ k) ≤ entropy ρ := by
      exact_mod_cast hbound
    have hQ : 0 ≤ ∑' k, spectralTerm ρ k := by
      apply tsum_nonneg
      intro k
      unfold spectralTerm frequencyLength
      positivity
    have hc : β / (2 * spectralThreshold d) ≤ (d : ℝ) / spectralThreshold d := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * spectralThreshold d)).mpr
      field_simp
      linarith
    have hm := mul_le_mul_of_nonneg_right hc hQ
    exact_mod_cast (show β / (2 * spectralThreshold d) * (∑' k, spectralTerm ρ k) - entropy ρ ≤ 0 by
      linarith)
  · have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hβ' : 0 < β := by linarith
    rw [pressure_eq_coefficientDefect (by omega) hβ']
    apply coefficient_below_infinite hd hd10
    unfold collapseCoefficient
    apply div_lt_div_of_pos_left hs (by positivity)
    have hp : 0 < (2 * Real.pi)^d := by positivity
    nlinarith

#print axioms circle_potential
#print axioms coefficient_formula
#print axioms potential_coefficient_sharp
#print axioms pressure_formula
end BecknerOnofri.HighDim.LowDimension
