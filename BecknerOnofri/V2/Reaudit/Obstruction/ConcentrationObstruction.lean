module

public import BecknerOnofri.V2.Reaudit.Obstruction.GreenEnergyLocalized
public import BecknerOnofri.V2.Reaudit.Obstruction.MollifierEntropy
public import BecknerOnofri.ConcentrationDivergence
public import BecknerOnofri.PressureDuality
public import BecknerOnofri.FiniteEntropyPhysical
public import BecknerOnofri.FiniteEntropyEnergy
public import BecknerOnofri.EndpointDuality
public import BecknerOnofri.LegacyBridge

@[expose] public section

/-! # Row S006, part (i): concentration, `P_d(β) = +∞` for `β > 2d` and `C_d(A) = +∞` for `A < A_c(d)`

Follows `lem:section2-universal-obstructions`(i):

1. the concentrating family `ρ_ε(x) = ε^{-d} η(x/ε)` (`mollified`) and its entropy
   `Ent(ρ_ε) = d log(1/ε) + ∫ η log η` (`AdmissibleProfile.entropy_mollified`);
2. the interaction `∬ G(x-y) ρ_ε(x) ρ_ε(y) ≥ log(1/ε) - O(1)`: the printed argument uses the
   Robin-constant expansion of `G` near the origin; here the lower bound with the same coefficient
   `1` is obtained from the Mellin heat representation
   (`green_pairing_localized_lower`, `physicalGreenEnergy_eq_integral_autocorrelation`);
3. assembly: `β c_d/2 ‖ρ_ε‖² - Ent(ρ_ε) ≥ (β/2 - d) log(1/ε) - O(1) → +∞`;
4. the passage from the pressure to the coefficient defect by
   `pressure_eq_coefficientDefect` (printed: Proposition `prop:section2-coefficient-pressure-duality`).

The profile used for the existence statement is the normalized indicator of the cube
`[-1/4, 1/4]^d`, which is bounded, nonnegative, of integral `1` and supported in the cube; the
printed smooth bump function is not needed because the argument uses only these four properties. -/

noncomputable section
open MeasureTheory Set

namespace BecknerOnofri.V2.Reaudit.Obstruction

open BecknerOnofri.HighDim

variable {d : ℕ}

/-! ### The mollified density as a probability density -/

/-- The mollification `ρ_ε` of an admissible profile, as a probability density on the torus. -/
def mollifiedDensity {η : (Fin d → ℝ) → ℝ} {M ε : ℝ} (h : AdmissibleProfile η M) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : Legacy.TorusEndpoint.ProbabilityDensity d where
  value := mollified η ε
  nonneg := Filter.Eventually.of_forall (mollified_nonneg h.nonneg hε)
  integrable := h.integrable_mollified hε
  mass := h.integral_mollified hε hε1

/-! ### The value of the pressure functional on a bounded density -/

/-- For a finite-entropy density, the pressure functional is `β/2` times the physical Green energy
minus the entropy. -/
lemma pressureValue_rawDensity (hd : 0 < d) (β : ℝ)
    (r : Legacy.TorusEndpoint.ProbabilityDensity d) (hr : r.FiniteEntropy) :
    pressureValue β (Bridge.rawDensity r) =
      ((β / 2 * Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy r -
        Legacy.TorusEndpoint.densityEntropy r.value : ℝ) : EReal) := by
  let ρ := Bridge.rawDensity r
  have hρ : ρ.FiniteEntropy := hr
  have he : Legacy.BecknerOnofri.fourierEnergy r = ∑' k, spectralTerm ρ k :=
    tsum_congr (Bridge.densitySpectralTerm_eq ρ)
  unfold pressureValue
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ, ← EReal.coe_mul, ← EReal.coe_sub]
  apply congrArg
  rw [FiniteEntropyPhysical.physical_eq_spectral hd r hr, Legacy.BecknerOnofri.normalized_energy,
    he]
  have hs : Legacy.TorusEndpoint.endpointSigma d = spectralThreshold d := rfl
  rw [hs]
  change β / (2 * spectralThreshold d) * (∑' k, spectralTerm ρ k) - entropy ρ =
    β / 2 * ((∑' k, spectralTerm ρ k) / spectralThreshold d) - entropy ρ
  ring

/-! ### The Green energy of the mollified density -/

/-- **Lower bound for the interaction of the concentrating family.**  There is a constant `K`,
depending only on `d`, such that for every admissible profile `η` and every `ε ≤ 1` with
`π d (ε/2)² ≤ 1`, `log(1/ε) + log 2 - K ≤ ∬ G(x - y) ρ_ε(x) ρ_ε(y)`. -/
theorem green_energy_mollified_lower (hd : 0 < d) :
    ∃ K : ℝ, ∀ {η : (Fin d → ℝ) → ℝ} {M ε : ℝ} (h : AdmissibleProfile η M) (hε : 0 < ε)
      (hε1 : ε ≤ 1) (hεsmall : Real.pi * d * (ε / 2) ^ 2 ≤ 1),
      Real.log (1 / ε) + Real.log 2 - K ≤
        Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy (mollifiedDensity h hε hε1) := by
  obtain ⟨K, hK⟩ := green_pairing_localized_lower hd
  refine ⟨K, ?_⟩
  intro η M ε h hε hε1 hεsmall
  set r := mollifiedDensity h hε hε1 with hr
  have hMf : ∀ x, r.value x ≤ (ε ^ d)⁻¹ * M := fun x => mollified_le h.le hε x
  have hf0 : ∀ x, 0 ≤ r.value x := mollified_nonneg h.nonneg hε
  have hfm : Measurable r.value := measurable_mollified h.measurable ε
  have hfi : Integrable r.value (torusMeasure d) := r.integrable
  have hf1 : ∫ x, r.value x ∂torusMeasure d = 1 := r.mass
  have hsupp : ∀ x, r.value x ≠ 0 → ∀ j, ‖x j‖ ≤ ε / 4 :=
    fun x hx => mollified_support h.support hε hx
  have hr2 : MemLp r.value 2 (torusMeasure d) :=
    (MemLp.of_bound hfm.aestronglyMeasurable ((ε ^ d)⁻¹ * M)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hMf x)).mono_exponent le_top
  rw [physicalGreenEnergy_eq_integral_autocorrelation r hr2]
  have key := hK (autocorrelation r.value) (ε / 2) ((ε ^ d)⁻¹ * M) (by positivity)
    hεsmall
    (measurable_autocorrelation hfm) (autocorrelation_nonneg hf0)
    (autocorrelation_le hfm hf0 hMf hfi hf1)
    (integral_autocorrelation hfm hf0 hMf hfi hf1)
    (fun z hz j => by
      have := autocorrelation_support (a := ε / 4) hsupp hz j
      linarith)
  have hlog : Real.log (1 / (ε / 2)) = Real.log (1 / ε) + Real.log 2 := by
    rw [show 1 / (ε / 2) = 2 * (1 / ε) by field_simp, Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [hlog] at key
  exact key

/-! ### An admissible profile, and the divergence of the pressure -/

/-- The normalized indicator of the cube `[-1/4, 1/4]^d`. -/
def cubeProfile (d : ℕ) : (Fin d → ℝ) → ℝ :=
  (Icc (fun _ : Fin d => -(1 / 4 : ℝ)) (fun _ => 1 / 4)).indicator (fun _ => (2 : ℝ) ^ d)

lemma cubeProfile_admissible (d : ℕ) : AdmissibleProfile (cubeProfile d) ((2 : ℝ) ^ d) where
  measurable := measurable_const.indicator measurableSet_Icc
  nonneg y := by
    unfold cubeProfile
    exact indicator_nonneg (fun _ _ => by positivity) y
  le y := by
    unfold cubeProfile
    by_cases hy : y ∈ Icc (fun _ : Fin d => -(1 / 4 : ℝ)) (fun _ => 1 / 4)
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]; positivity
  support y hy j := by
    have hm : y ∈ Icc (fun _ : Fin d => -(1 / 4 : ℝ)) (fun _ => 1 / 4) := by
      by_contra h
      exact hy (indicator_of_notMem h _)
    exact abs_le.mpr ⟨hm.1 j, hm.2 j⟩
  mass := by
    unfold cubeProfile
    rw [integral_indicator_const _ measurableSet_Icc, Measure.real,
      Real.volume_Icc_pi_toReal (fun j => by norm_num)]
    simp only [smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← mul_pow]
    norm_num

/-- **Concentration, part of `lem:section2-universal-obstructions`(i):** for `β > 2d` the pressure is
`+∞`. -/
theorem pressure_eq_top_of_critical_lt (hd : 0 < d) {β : ℝ} (hβ : 2 * (d : ℝ) < β) :
    pressure d β = ⊤ := by
  obtain ⟨K, hK⟩ := green_energy_mollified_lower hd
  have hη := cubeProfile_admissible d
  set H : ℝ := ∫ y, cubeProfile d y * Real.log (cubeProfile d y) with hH
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hπd : (1 : ℝ) ≤ Real.pi * d := by
    have := Real.pi_gt_three
    have : (1 : ℝ) ≤ d := Nat.one_le_cast.mpr hd
    nlinarith
  have hπpos : 0 < Real.pi * d := by linarith
  set A : ℝ := β / 2 - d with hA
  have hApos : 0 < A := by rw [hA]; linarith
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  set C₀ : ℝ := β / 2 * (K - Real.log 2) + H with hC₀
  set t : ℝ := max (Real.log (Real.pi * d)) (|M + C₀| / A + 1) with ht
  set ε : ℝ := Real.exp (-t) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have ht0 : Real.log (Real.pi * d) ≤ t := le_max_left _ _
  have hεle : ε * (Real.pi * d) ≤ 1 := by
    have h1 : ε ≤ (Real.pi * d)⁻¹ := by
      rw [hε, ← Real.exp_log (inv_pos.mpr hπpos), Real.log_inv]
      exact Real.exp_le_exp.mpr (by linarith)
    calc ε * (Real.pi * d) ≤ (Real.pi * d)⁻¹ * (Real.pi * d) :=
          mul_le_mul_of_nonneg_right h1 hπpos.le
      _ = 1 := inv_mul_cancel₀ hπpos.ne'
  have hε1 : ε ≤ 1 := by nlinarith
  have hsmall : Real.pi * d * (ε / 2) ^ 2 ≤ 1 := by
    have : Real.pi * d * (ε / 2) ^ 2 = (ε * (Real.pi * d)) * ε / 4 := by ring
    rw [this]
    nlinarith
  have hlogε : Real.log (1 / ε) = t := by
    rw [hε, one_div, ← Real.exp_neg, Real.log_exp, neg_neg]
  set r := mollifiedDensity hη hεpos hε1 with hr
  have hfin : r.FiniteEntropy := hη.integrable_mollified_mul_log hεpos
  have hE := hK hη hεpos hε1 hsmall
  have hEnt : Legacy.TorusEndpoint.densityEntropy r.value = d * t + H := by
    have := hη.entropy_mollified hεpos hε1
    rw [hlogε] at this
    exact this
  have hval := pressureValue_rawDensity hd β r hfin
  have hbound : (M : ℝ) < β / 2 * Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy r -
      Legacy.TorusEndpoint.densityEntropy r.value := by
    rw [hEnt]
    rw [hlogε] at hE
    have h1 : β / 2 * (t + Real.log 2 - K) ≤
        β / 2 * Legacy.TorusEndpoint.PhysicalGreenL2.physicalGreenEnergy r :=
      mul_le_mul_of_nonneg_left hE (by linarith)
    have h2 : |M + C₀| / A + 1 ≤ t := le_max_right _ _
    have h3 : |M + C₀| + A ≤ A * t := by
      have := mul_le_mul_of_nonneg_left h2 hApos.le
      have e : A * (|M + C₀| / A + 1) = |M + C₀| + A := by field_simp
      linarith
    have h4 : M + C₀ ≤ |M + C₀| := le_abs_self _
    have h5 : A * t = β / 2 * t - d * t := by rw [hA]; ring
    nlinarith
  have hpv : (M : EReal) < pressureValue β (Bridge.rawDensity r) := by
    rw [hval]
    exact EReal.coe_lt_coe_iff.mpr hbound
  exact hpv.trans_le (le_iSup_of_le (Bridge.rawDensity r) (le_iSup_of_le hfin le_rfl))

/-- **Concentration, part of `lem:section2-universal-obstructions`(i), coefficient form:** for
`A < A_c(d) = 1/(4 d c_d)` the optimal additive defect is `+∞`. -/
theorem coefficientDefect_eq_top_of_lt_critical (hd : 0 < d) {A : ℝ}
    (hA : A < collapseCoefficient d) : coefficientDefect d A = ⊤ := by
  have hσ := spectralThreshold_pos hd
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hc : 0 < collapseCoefficient d := by unfold collapseCoefficient; positivity
  obtain ⟨B, hB, hBc⟩ := exists_between (max_lt hA hc)
  have hBp : 0 < B := (le_max_right A 0).trans_lt hB
  have hAB : A ≤ B := ((le_max_left A 0).trans_lt hB).le
  let β := spectralThreshold d / (2 * B * (2 * Real.pi) ^ d)
  have hβp : 0 < β := by dsimp [β]; positivity
  have hβ : 2 * (d : ℝ) < β := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * B * (2 * Real.pi) ^ d)).mpr
    unfold collapseCoefficient at hBc
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * (d : ℝ) * (2 * Real.pi) ^ d)).mp hBc
    nlinarith
  have he : spectralThreshold d / (2 * β * (2 * Real.pi) ^ d) = B := by
    dsimp [β]
    field_simp
  have hInf := pressure_eq_top_of_critical_lt hd hβ
  rw [pressure_eq_coefficientDefect hd hβp, he] at hInf
  apply top_le_iff.mp
  rw [← hInf]
  exact coefficientDefect_antitone hd hAB

end BecknerOnofri.V2.Reaudit.Obstruction
