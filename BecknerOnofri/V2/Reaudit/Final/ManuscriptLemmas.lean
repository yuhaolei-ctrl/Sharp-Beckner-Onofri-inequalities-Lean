module

public import BecknerOnofri.V2.Reaudit.Final.All
public import BecknerOnofri.V2.Reaudit.Final.ManuscriptTheorems
public import BecknerOnofri.V2.Vocab.Section2Heat
public import BecknerOnofri.V2.Reaudit.ShellMargins.Theta
public import BecknerOnofri.V2.Reaudit.ShellMargins.LowScalarGap
public import BecknerOnofri.V2.Reaudit.Mixtures.PrintedGap
public import BecknerOnofri.V2.Rearrangement.Comparison
public import BecknerOnofri.V2.Reaudit.Attainment.Main
public import BecknerOnofri.V2.Reaudit.Attainment.Pairing

@[expose] public section

/-! # Printed Section 2 lemmas as roots (Reaudit, Final)

Leaf module: new printed-statement roots, each stating a displayed lemma/equation of the manuscript
(SHA-256 1a3b8bdb...) and proved from the route declarations, so that these declarations are ancestors
of a root.  Rows:

* U24, U03 (`eq:section2-critical-adams`, `eq:section2-all-exponential-moments`):
  `lem_section2_critical_adams`, `lem_section2_all_exponential_moments`;
* S007 (`lem:section2-weak-beckner-onofri`, `eq:section2-positive-threshold-input`, `β_gm(d) > 0`):
  `lem_section2_weak_beckner_onofri`, `eq_section2_positive_threshold_input`,
  `section2_globalTransition_pos`;
* S018 (`lem:circle-entropy`): `lem_circle_entropy`;
* S004 (`lem:section2-finite-entropy-energy`): `lem_section2_finite_entropy_energy`;
* S022 (`lem:theta-integral-certificate`): `lem_theta_integral_certificate_printed`;
* S023 (`prop:equality`): `prop_equality_root`;
* S012 (`lem:coordinate-rearranged-minimizer`): `lem_coordinate_rearranged_minimizer_root`;
* S016 (`lem:selection-full-entropy-domain`): `lem_selection_full_entropy_domain_printed`. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri
open HighDim
open V2.Vocab

namespace V2.Reaudit.Final

/-! ## Rows U24 and U03 -/

/-- **`eq:section2-critical-adams`** (rows U24, U03), all `d ≥ 1`: there is `B` with
`log ∫ e^{u-ū} ≤ A_crit(d) ‖u‖²_{Ḣ^{d/2}} + B` for all `u ∈ H^{d/2}`, in the printed normalization
`A_crit(d) = 1/(4 d c_d)` and in the repository shape `collapseCoefficient d * potentialEnergy u`. -/
theorem lem_section2_critical_adams {d : ℕ} (hd : 0 < d) :
    (∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤
        (((1 / (4 * (d : ℝ) * kernelConstant d)) * (sobolevEnergyPos u).toReal + B : ℝ) : EReal)) ∧
    (∃ B : ℝ, ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((collapseCoefficient d * potentialEnergy u + B : ℝ) : EReal)) :=
  ⟨ExternalInputs.criticalAdams hd,
    (V2.Vocab.criticalAdamsInput_iff hd).1 (ExternalInputs.criticalAdams hd)⟩

/-- **`eq:section2-all-exponential-moments`** (row U03): `e^{p|u|} ∈ L¹(𝕋^d)` for every
`u ∈ H^{d/2}` and every `1 ≤ p < ∞`.  Proof as in the manuscript: `e^{p|u|} ≤ e^{pu} + e^{-pu}` and
the rough exponential estimate `lem:section2-rough-exponential` applied to `u` and to `-u`
(`Attainment.integrable_exp_mul_abs`, which rests on `GenericAttainment.rough_bound`); the sharp
critical Adams inequality is not used.  The constant `ū` is removed first, since `|u| ≤ |ū| + |u - ū|`. -/
theorem lem_section2_all_exponential_moments {d : ℕ} (hd : 0 < d) {u : Torus d → ℝ}
    (hu : InCriticalSobolev u) {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun x => Real.exp (p * |u x|)) (torusMeasure d) := by
  have hc : InCriticalSobolev (centered u) := Attainment.inCriticalSobolev_centered hu
  have hm : MeanZero (centered u) := Attainment.meanZero_centered hu.1
  have h := Attainment.integrable_exp_mul_abs hd hc hm p
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (p * |u x|)) (torusMeasure d) :=
    Real.continuous_exp.comp_aestronglyMeasurable
      ((hu.1.aestronglyMeasurable.norm.const_mul p).congr
        (Filter.Eventually.of_forall fun x => by simp))
  refine (h.const_mul (Real.exp (p * |∫ y, u y ∂torusMeasure d|))).mono' hmeas
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : |u x| ≤ |∫ y, u y ∂torusMeasure d| + |centered u x| := by
    have := abs_add_le (∫ y, u y ∂torusMeasure d) (centered u x)
    have e : (∫ y, u y ∂torusMeasure d) + centered u x = u x := by simp [centered]
    rwa [e] at this
  nlinarith

/-! ## Row S016 -/

/-- **`lem:selection-full-entropy-domain`** (row S016), `d ≥ 2`, `0 < β < 2d`: existence of a global
minimizer of `ℰ_β`, smoothness, strict positivity and the Gibbs/Euler form of every minimizer, and the
entropy-preserving canonical selection of a coordinatewise even and nonincreasing minimizer that is a
countable cosine mixture with nonnegative Fourier coefficients.  The Lean statement is stated for `d ≥ 1`. -/
theorem lem_selection_full_entropy_domain_printed {d : ℕ} (hd : 2 ≤ d) :
    type_of% (V2.Reaudit.Mixtures.selection_full_entropy_domain_written (d := d) (by omega)) :=
  V2.Reaudit.Mixtures.selection_full_entropy_domain_written (by omega)

/-! ## Row S007 -/

/-- **`lem:section2-weak-beckner-onofri`** (row S007): there is `A₀ > 0` with
`log ∫ e^{u-ū} ≤ A₀ ‖u‖²_{Ḣ^{d/2}}` for every `u ∈ H^{d/2}` (no additive constant). -/
theorem lem_section2_weak_beckner_onofri {d : ℕ} (hd : 0 < d) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ u : Torus d → ℝ, InCriticalSobolev u →
      Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) ≤ A₀ * potentialEnergy u :=
  ExternalInputs.exists_weak_beckner_onofri hd

/-- **`eq:section2-positive-threshold-input`** (row S007), all `d ≥ 1`: there is `β₀ > 0` with
`Ent(ρ) ≥ (β₀ c_d / 2) ‖ρ‖²_{Ḣ^{-d/2}}` for every finite-entropy density; for `d = 1` one may take
`β₀ = 2` (Lebedev--Milin). -/
theorem eq_section2_positive_threshold_input {d : ℕ} (hd : 0 < d) :
    (∃ β₀ : ℝ, 0 < β₀ ∧ ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      β₀ * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal ≤
        (torusEntropy ρ.value).toReal) ∧
    (d = 1 → ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (2 : ℝ) * kernelConstant d / 2 * (negSobolevEnergy ρ.value).toReal ≤
        (torusEntropy ρ.value).toReal) := by
  refine ⟨ExternalInputs.positiveThreshold_independent_print hd, ?_⟩
  rintro rfl ρ hρ
  have h := ExternalInputs.circleLebedevMilin ρ hρ
  have e : (2 : ℝ) * kernelConstant 1 / 2 = kernelConstant 1 := by ring
  rw [e]
  exact h

/-- **`β_gm(d) > 0`** (row S007), from `eq:section2-positive-threshold-input`. -/
theorem section2_globalTransition_pos {d : ℕ} (hd : 0 < d) :
    0 < VariationalCurves.globalTransition d :=
  V2.Vocab.globalTransition_pos_of_input hd (ExternalInputs.positiveThreshold_independent_print hd)

/-! ## Row S018 -/

/-- **`lem:circle-entropy`** (row S018), in the repository normalization: for every finite-entropy
density on `𝕋¹`, `c_1 ‖ρ‖²_{Ḣ^{-1/2}} ≤ Ent(ρ)` (equivalently `Σ_{n≥1} |ρ̂(n)|²/n ≤ Ent(ρ)`). -/
theorem lem_circle_entropy :
    ∀ ρ : ProbabilityDensity 1, ρ.FiniteEntropy →
      kernelConstant 1 * (negSobolevEnergy ρ.value).toReal ≤ (torusEntropy ρ.value).toReal :=
  ExternalInputs.circleLebedevMilin


/-! ## Row S004 -/

/-- **`lem:section2-finite-entropy-energy`** (row S004), every assertion: for a finite-entropy density
the negative Sobolev energy is finite and `0 ≤ c_d‖ρ‖² ≤ (2/a) Ent(ρ) + (1/a) log ∬ e^{aγ}` for every
`a ∈ (0,d)` (`eq:section2-finite-entropy-energy-bound`); along the heat regularization `ρ_t` (`t ↓ 0`)
`Ent(ρ_t) → Ent(ρ)` (`eq:section2-entropy-heat-approximation`) and `‖ρ_t‖² → ‖ρ‖²`
(`eq:section2-energy-heat-approximation`, also in the form `c_d‖ρ_t‖² → c_d‖ρ‖²`); and for every `t > 0`
`ρ_t` is the value of a finite-entropy density that is smooth and strictly positive. -/
theorem lem_section2_finite_entropy_energy {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    (∀ a : ℝ, 0 < a → a < (d : ℝ) →
      negSobolevEnergy ρ.value ≠ ∞ ∧
        0 ≤ kernelConstant d * (negSobolevEnergy ρ.value).toReal ∧
        kernelConstant d * (negSobolevEnergy ρ.value).toReal ≤
          2 / a * (torusEntropy ρ.value).toReal + 1 / a * Real.log
            (∫ x, ∫ y, Real.exp (a * Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y))
              ∂torusMeasure d ∂torusMeasure d)) ∧
    Tendsto (fun t : ℝ => torusEntropy (heatRegularization ρ t)) (𝓝[>] (0 : ℝ))
      (𝓝 (torusEntropy ρ.value)) ∧
    Tendsto (fun t : ℝ => negSobolevEnergy (heatRegularization ρ t)) (𝓝[>] (0 : ℝ))
      (𝓝 (negSobolevEnergy ρ.value)) ∧
    Tendsto (fun t : ℝ => kernelConstant d * (negSobolevEnergy (heatRegularization ρ t)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (kernelConstant d * (negSobolevEnergy ρ.value).toReal)) ∧
    (∀ t : ℝ, 0 < t → ∃ η : ProbabilityDensity d, η.value = heatRegularization ρ t ∧
      η.FiniteEntropy ∧ SmoothOnTorus η.value ∧ ∀ x, 0 < η.value x) :=
  ⟨fun _ ha had => V2.Vocab.finite_entropy_energy_bound hd ρ hρ ha had,
    V2.Vocab.heat_entropy_tendsto_nhdsGT ρ hρ,
    V2.Vocab.heat_negSobolevEnergy_tendsto_nhdsGT hd ρ hρ,
    V2.Vocab.heat_energy_real_tendsto_nhdsGT hd ρ hρ,
    fun _ ht => heatRegularization_regular ρ ht⟩

/-! ## Row S022 -/

/-- **`lem:theta-integral-certificate`** (row S022): `J_10 ≤ 41/25`, with
`J_d = ∫_1^∞ (r^{d/2-1} + r⁻¹)(ϑ(πr)^d - 1) dr`. -/
theorem lem_theta_integral_certificate_printed :
    LowScalar.thetaIntegral 10 ≤ (41 / 25 : ℝ) :=
  V2.Reaudit.ShellMargins.lem_theta_integral_certificate

/-- **`eq:scalar-result`** (rows S020, S022, shell-margin chain): for `2 ≤ d ≤ 10` and `n ≥ 1`,
`d H_n - (2d/β_s(d)) G_{d,n} > 3/1100`, from the retained-shell certificate (171 pairs), the
two-dimensional estimate and the theta-integral bound `J_10 ≤ 41/25`. -/
theorem eq_scalar_result_printed (d n : ℕ) (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n) :
    (3 / 1100 : ℝ) < (d : ℝ) * (_root_.harmonic n : ℝ) -
      (2 * (d : ℝ) / spectralThreshold d) * LowScalar.energy d n :=
  V2.Reaudit.ShellMargins.low_scalar_gap d n hd2 hd10 hn

/-! ## Row S023 -/

/-- **`prop:equality`** (Proposition 3.7, row S023), as printed: for `2 ≤ d ≤ 10`, equality in the
dual entropy inequality `d c_d ‖ρ‖²_{Ḣ^{-d/2}} = Ent(ρ)` for a finite-entropy density holds only for the
uniform density, and equality in the potential inequality for `u ∈ H^{d/2}` holds only for constants. -/
theorem prop_equality_root (d : ℕ) (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (d : ℝ) * kernelConstant d * (negSobolevEnergy ρ.value).toReal =
        (torusEntropy ρ.value).toReal → ρ.value =ᵐ[torusMeasure d] fun _ => 1) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) →
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c) :=   by
  obtain ⟨h1, h2⟩ := V2.Reaudit.Mixtures.prop_3_7_aligned hd2 hd10
  exact ⟨fun ρ hρ h => (h1 ρ hρ).1 h, fun u hu h => (h2 u hu).1 h⟩

/-! ## Row S012 -/

/-- **`lem:coordinate-rearranged-minimizer`** (row S012), as printed: for `0 < β < 2d` there is a smooth
strictly positive minimizer `r` of the free energy, obtained as the coordinate rearrangement of a smooth
initial minimizer `ρ₀` (Proposition `prop:section2-subcritical-attainment`), such that `r` and its
potential `u_r = β g ∗ r` are separately even and nonincreasing in each coordinate. -/
theorem lem_coordinate_rearranged_minimizer_root (d : ℕ) (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (hβd : β < 2 * (d : ℝ)) :
    ∃ (ρ₀ r : ProbabilityDensity d) (u : Torus d → ℝ),
      IsGlobalMinimizer β ρ₀ ∧ SmoothOnTorus ρ₀.value ∧ (∀ x, 0 < ρ₀.value x) ∧
      V2.Rearrangement.MeasSuccessive ρ₀.value r.value ∧ IsGlobalMinimizer β r ∧
      ProbabilityTheory.IdentDistrib r.value ρ₀.value (torusMeasure d) (torusMeasure d) ∧
      entropy r = entropy ρ₀ ∧ spectralEnergy r = spectralEnergy ρ₀ ∧
      SmoothOnTorus r.value ∧ (∀ x, 0 < r.value x) ∧ r.value = normalizedGibbs u ∧
      SmoothOnTorus u ∧ MeanZero u ∧ u =ᵐ[torusMeasure d] Gap.densityPotential β r.value ∧
      PrescribedSelection.CoordinateSteiner r.value ∧ PrescribedSelection.CoordinateSteiner u :=
  V2.Rearrangement.coordinate_rearranged_minimizer_printed hd hβ hβd

#print axioms lem_section2_critical_adams
#print axioms lem_section2_all_exponential_moments
#print axioms lem_selection_full_entropy_domain_printed
#print axioms lem_section2_weak_beckner_onofri
#print axioms eq_section2_positive_threshold_input
#print axioms section2_globalTransition_pos
#print axioms lem_circle_entropy
#print axioms lem_section2_finite_entropy_energy
#print axioms lem_theta_integral_certificate_printed
#print axioms eq_scalar_result_printed
#print axioms prop_equality_root
#print axioms lem_coordinate_rearranged_minimizer_root

end V2.Reaudit.Final
end BecknerOnofri

end
