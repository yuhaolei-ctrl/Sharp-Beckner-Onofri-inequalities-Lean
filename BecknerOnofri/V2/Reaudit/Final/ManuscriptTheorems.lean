module

public import BecknerOnofri.V2.Reaudit.Final.All
public import BecknerOnofri.V2.Reaudit.Final.ManuscriptLemmas2

@[expose] public section

/-! # Theorems 1.1 and 1.3 as printed (Reaudit, Final)

Each theorem below states, as one conjunction, every assertion of the corresponding printed theorem of
the manuscript (SHA-256 1a3b8bdb...), and is proved from the route-aligned declarations.  The
Challenge-shaped regression targets are unchanged; these are added next to them.  Theorem 1.2 is `theorem_1_2_printed` (statement
`V2.Eleven.theorem_1_2` together with `V2.Final.eleven_competitor_written`, both printed constants), assembled
directly from `prop41_route`, `prop49_route` and the printed-route bounds. Theorem 1.3 is `theorem_1_3_printed`,
whose threshold and inequality assertions are read off from `high_endpoint_printed`
(`cor:section5-high-endpoint`). -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace BecknerOnofri
open HighDim

namespace V2.Reaudit.Final

/-- **Theorem 1.1** (dimensions `1 ≤ d ≤ 10`), every assertion of the printed statement:
the primal inequality (eq:intro-low-primal), the dual inequality (eq:intro-low-dual), sharpness of the
coefficient, the equality classification (the circle family for `d = 1`, constants for `2 ≤ d ≤ 10`),
and the consequences (eq:intro-low-coefficient-consequence). -/
theorem theorem_1_1_printed (d : ℕ) (hd : 1 ≤ d) (hd10 : d ≤ 10) :
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) ∧
    (∀ ρ : ProbabilityDensity d,
      (((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤
        extendedEntropy ρ) ∧
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) ∧
    (d = 1 →
      (∀ u : Torus 1 → ℝ, InCriticalSobolev u →
        (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
          ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ,
            u =ᵐ[torusMeasure 1] fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c)) ∧
      (∀ ρ : ProbabilityDensity 1, ρ.FiniteEntropy →
        ((((1 : ℝ) / spectralThreshold 1 : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
            (entropy ρ : EReal) ↔
          ∃ a : ℂ, ‖a‖ < 1 ∧
            ρ.value =ᵐ[torusMeasure 1] fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2))) ∧
    (2 ≤ d →
      (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
        ((((d : ℝ) / spectralThreshold d : ℝ) : EReal) * (spectralEnergy ρ).toEReal =
            (entropy ρ : EReal) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
      (∀ u : Torus d → ℝ, InCriticalSobolev u →
        (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c))) ∧
    (∀ β : ℝ, pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤) ∧
    (∀ A : ℝ, coefficientDefect d A = if collapseCoefficient d ≤ A then 0 else ⊤) ∧
    VariationalCurves.globalTransition d = 2 * (d : ℝ) := by
  refine ⟨fun u hu => Mixtures.low_dim_beckner_onofri d hd hd10 u hu,
    fun ρ => Mixtures.low_dim_entropy_inequality d hd hd10 ρ,
    Mixtures.low_dim_coefficient_sharp d hd hd10, ?_, ?_,
    fun β => Mixtures.low_dim_pressure_eq d hd hd10 β,
    fun A => Mixtures.low_dim_defect_eq d hd hd10 A,
    Mixtures.low_dim_globalTransition d hd hd10⟩
  · intro h1
    subst h1
    exact ⟨fun u hu => Mixtures.circle_beckner_onofri_eq_iff u hu,
      fun ρ hρ => Mixtures.circle_entropy_eq_iff ρ hρ⟩
  · intro h2
    exact ⟨fun ρ hρ => Mixtures.low_dim_entropy_eq_iff d h2 hd10 ρ hρ,
      fun u hu => Mixtures.low_dim_beckner_onofri_eq_iff d h2 hd10 u hu⟩

/-- **Theorem 1.3** (dimensions `d ≥ 12`), every assertion of the printed statement: the dual and
primal inequalities with their equality cases, the thresholds (eq:intro-high-threshold), `κ_d > 0`, the
Morse--Bott branch with the cosine expansion and the translation-orbit classification of the global
minimizers, the pressure onset (eq:intro-pressure-onset), the defect onset (eq:intro-C-onset), the
embedded critical manifold, the exact quadratic cosine correction, the one-sided second derivatives of
the pressure, the first-shell order parameter, and the identification of the branches. -/
theorem theorem_1_3_printed (d : ℕ) (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d,
      ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ) ∧
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    (IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
      IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) ∧
      VariationalCurves.globalTransition d = spectralThreshold d ∧
      VariationalCurves.zeroDefectCoefficient d = spectralCoefficient d) ∧
    0 < kappa d ∧
    FullBranchOnset d ∧
    (∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3) ∧
    (∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3) ∧
    type_of% (Onset.onset_manuscript d hd) :=
  ⟨fun ρ => high_dim_entropy_inequality_printed d hd ρ,
    fun ρ hρ => ((high_endpoint_printed d hd).1 ρ hρ).2,
    fun u hu => ⟨((high_endpoint_printed d hd).2.1 u hu).1, ((high_endpoint_printed d hd).2.1 u hu).2.1⟩,
    fun u hu => ((high_endpoint_printed d hd).2.1 u hu).2.2,
    high_dim_thresholds_printed d hd,
    V2.Final.kappa_pos d hd,
    Onset.high_dim_onset_branch_route d hd,
    Onset.high_dim_pressure_onset_route d hd,
    Onset.high_dim_defect_onset_route d hd,
    Onset.onset_manuscript d hd⟩


/-- `C_11(A_s) = P_11(β_s) > 1/30` (first display of `eq:intro-d11-threshold`) from the two printed
certificates: the entropy bound `Ent(ρ_*) < 8653/600` (`ElevenBounds.torusEntropy_bound_printed`) and the
shell-expansion energy bound `(2π)^{11}/2 ‖ρ_*‖² > 14475384292906/10^{12}`
(`ElevenBounds.energy_bound_via_shells`), inserted into the free energy of the competitor `ρ_*` at `β_s`:
`P_11(β_s) ≥ (2π)^{11}/2 ‖ρ_*‖² − Ent(ρ_*) > 579/40 − 8653/600 = 4/75 > 1/30`. -/
theorem spectral_pressure_gt_thirtieth_printed :
    (((1 : ℝ) / 30 : ℝ) : EReal) < pressure 11 (spectralThreshold 11) := by
  have h := V2.Eleven.rhoStar_value
  have hρ := V2.Eleven.finiteEntropy_of_value_eq _ h
  have hv := HighDim.Eleven.pressureValue_le_pressure (spectralThreshold 11) V2.Eleven.rhoStar hρ
  rw [V2.Eleven.pressureValue_eq_real_ms (by norm_num) _ _ hρ] at hv
  have hcs := V2.Vocab.kernelConstant_mul_spectralThreshold (d := 11) (by norm_num)
  have e : spectralThreshold 11 * V2.Vocab.kernelConstant 11 / 2 *
      (V2.Vocab.negSobolevEnergy V2.Eleven.rhoStar.value).toReal =
        (2 * Real.pi) ^ 11 / 2 * (V2.Vocab.negSobolevEnergy V2.Eleven.rhoStar.value).toReal := by
    rw [mul_comm (spectralThreshold 11), hcs]
  rw [e] at hv
  refine lt_of_lt_of_le ?_ hv
  have h1 := ElevenBounds.energy_bound_via_shells _ h
  have h2 := ElevenBounds.torusEntropy_bound_printed _ h
  have h3 : (579 : ℝ) / 40 < 14475384292906 / 10 ^ 12 := by norm_num
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-- **Theorem 1.2** (`thm:intro-d11`), every assertion of the printed statement, together with the
certificate `eq:intro-d11-certificate` (entropy bound `Ent(ρ_*) < 8653/600` and `2·144753/10000 < ‖ρ_*‖²`),
along the route of the print: Proposition 4.1 (`d11:thm:interval`) in the printed order, the lattice-label
and shell-expansion bounds, and Proposition 4.9 (`prop:section4-first-order-coexistence`) from the
compactness argument (`prop41_route`, `prop49_route`). -/
theorem theorem_1_2_printed :
    type_of% V2.Eleven.theorem_1_2 ∧ type_of% V2.Final.eleven_competitor_written := by
  have hv := prop41_route
  have h49 := prop49_route
  have hsm : SmoothOnTorus V2.Eleven.rhoStar.value := V2.Eleven.periodizedProfile_smooth_of_M_test
  have h : type_of% V2.Eleven.theorem_1_2 :=
    ⟨⟨V2.Eleven.rhoStar_value, V2.Eleven.finiteEntropy_of_value_eq _ V2.Eleven.rhoStar_value, hsm,
        fun x => HighDim.Eleven.periodizedProfile_pos x,
        ElevenBounds.torusEntropy_bound_printed _ V2.Eleven.rhoStar_value,
        ElevenBounds.energy_bound_via_shells _ V2.Eleven.rhoStar_value⟩,
      ⟨V2.Eleven.defect_spectral_eq_pressure, spectral_pressure_gt_thirtieth_printed⟩,
      ⟨hv.1.1, hv.1.2, V2.Eleven.upper_lt_spectral.1, V2.Eleven.upper_lt_spectral.2⟩, h49.1,
      h49.2.1, h49.2.2.1.2, h49.2.2.2.1.2⟩
  refine ⟨h, ?_⟩
  have hv := V2.Eleven.rhoStar_value
  have hc := h.1
  refine ⟨V2.Eleven.rhoStar, hv, hc.2.2.1, hc.2.2.2.1, hc.2.1, ?_, eleven_energy_gt_route _ hv⟩
  rw [V2.Vocab.entropy_eq_toReal_torusEntropy _ hc.2.1]
  exact hc.2.2.2.2.1

/-- **Lemma `lem:section2-universal-obstructions`, all five assertions as printed** (with `0 ≤` and finiteness
of the defect at the concentration coefficient): the pressure is infinite beyond `2d`, the defect is
infinite below `A_c(d)`, it is finite and nonnegative at `A_c(d)`, and the pressure and the defect are
positive above `β_s(d)` and below `A_s(d)`, respectively. -/
theorem lem_section2_universal_obstructions (d : ℕ) (hd : 1 ≤ d) :
    (∀ β : ℝ, 2 * (d : ℝ) < β → pressure d β = ⊤) ∧
    (∀ A : ℝ, A < collapseCoefficient d → coefficientDefect d A = ⊤) ∧
    (0 ≤ coefficientDefect d (collapseCoefficient d) ∧
      coefficientDefect d (collapseCoefficient d) ≠ ⊤) ∧
    (∀ β : ℝ, spectralThreshold d < β → 0 < pressure d β) ∧
    (∀ A : ℝ, A < spectralCoefficient d → 0 < coefficientDefect d A) := by
  have h := Obstruction.universal_obstructions_unconditional (d := d) hd
  exact ⟨h.1, h.2.1, ⟨coefficientDefect_nonneg d _, h.2.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩

#print axioms lem_section2_universal_obstructions

#print axioms theorem_1_1_printed
#print axioms theorem_1_2_printed
#print axioms theorem_1_3_printed

end V2.Reaudit.Final
end BecknerOnofri

end
