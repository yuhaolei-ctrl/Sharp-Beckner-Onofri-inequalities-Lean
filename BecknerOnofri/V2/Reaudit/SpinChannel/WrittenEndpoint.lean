module

public import BecknerOnofri.V2.Final.Unconditional

@[expose] public section

/-! # Corollary 5.8 (`cor:section5-high-endpoint`) through the written dimension transfer (SpinChannel package, S040)

The existing `Assembly.high_endpoint` / `Final.Unconditional.high_endpoint` obtain the density
inequality and its equality case in dimension `d ≥ 12` from `Transfer.spectral_dimension_transfer`
(the repository `d → d+1` induction on cosine mixtures) and obtain the remaining conjuncts from
`MixtureEndpoint 12` (`pressure_threshold_from_twelve`, `potential_endpoint_from_twelve`, ...), which
are again built on the `d → d+1` mixture induction.

Here every conjunct is derived from the dimension-`d` density statement alone, which is
`Transfer.spectral_dimension_transfer_written` (Proposition 5.7 along the written chain: selected minimizing
mixture, Proposition 5.5 and Lemma 5.2 at `r = 12`, the `d = 12` hypotheses on the transported marginals):

* the potential inequality and integrability: `potential_endpoint_of_density`;
* equality only for constants: `potential_rigidity_of_density`;
* `IsGreatest` of the zero-pressure set: `pressure_threshold_of_density`;
* `IsLeast` of the zero-defect coefficient set: `coefficient_threshold_of_density`;
* `globalTransition d = spectralThreshold d`: `IsGreatest.csSup_eq`, as in `Assembly.high_endpoint`.

Each statement is `rfl`-identical to the corresponding declaration of `Assembly` / `Final.Unconditional`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.V2

/-- Proposition 5.7 + Proposition 5.1 for `d ≥ 12`, via the written transfer.  Same type as
`Assembly.spectral_high_density`. -/
theorem spectral_high_density_written (hsc : Assembly.ScalarBounds) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1) :=
  Transfer.spectral_dimension_transfer_written (Assembly.spectralD12Inequality hsc)
    (Assembly.spectralD12Equality hsc) hd ρ hρ

/-- **Corollary 5.8 (`cor:section5-high-endpoint`)** through the written dimension transfer.  Same type as
`Assembly.high_endpoint`. -/
theorem high_endpoint_written_of_scalarBounds (hsc : Assembly.ScalarBounds) {d : ℕ} (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
        (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ∧
        (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
    VariationalCurves.globalTransition d = spectralThreshold d ∧
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) := by
  have hd0 : 0 < d := by omega
  have hE : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) :=
    fun ρ hρ => (spectral_high_density_written hsc hd ρ hρ).1
  have hR : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) → ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
    fun ρ hρ h => ((spectral_high_density_written hsc hd ρ hρ).2).mp h
  have hthr := pressure_threshold_of_density hd0 hE
  refine ⟨fun ρ hρ => spectral_high_density_written hsc hd ρ hρ, fun u hu => ?_, hthr, ?_,
    coefficient_threshold_of_density hd0 hE⟩
  · obtain ⟨hi, hle⟩ := potential_endpoint_of_density hd0 hE u hu
    exact ⟨hi, hle, potential_rigidity_of_density hd0 hE hR u hu⟩
  · exact hthr.csSup_eq

/-- The written-transfer endpoint and `Assembly.high_endpoint` have literally the same statement. -/
theorem high_endpoint_written_of_scalarBounds_statement_eq :
    (type_of% @high_endpoint_written_of_scalarBounds) = (type_of% @Assembly.high_endpoint) := rfl

/-- **Onset inputs** (inequality and forward equality of Corollary 5.8) via the written transfer.  Same type as
`Final.Unconditional.onsetEndpointInputs`. -/
theorem onsetEndpointInputs_written {d : ℕ} (hd : 12 ≤ d) : Onset.OnsetEndpointInputs d :=
  ⟨fun ρ hρ => (spectral_high_density_written Final.Unconditional.scalarBounds hd ρ hρ).1,
    fun ρ hρ h => ((spectral_high_density_written Final.Unconditional.scalarBounds hd ρ hρ).2).mp h⟩

/-- **Corollary 5.8 (`cor:section5-high-endpoint`), hypothesis-free, through the written dimension transfer.**
Same type as `Final.Unconditional.high_endpoint`. -/
theorem high_endpoint_written (d : ℕ) (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
        (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ∧
        (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
    VariationalCurves.globalTransition d = spectralThreshold d ∧
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) :=
  high_endpoint_written_of_scalarBounds Final.Unconditional.scalarBounds hd

theorem high_dim_entropy_inequality_written (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ := by
  refine Final.ereal_le_extendedEntropy (by omega) ρ _ fun hρ => ?_
  have h := (high_endpoint_written d hd).1 ρ hρ |>.1
  have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top (by omega) ρ hρ
  have h2 : (spectralEnergy ρ).toReal ≤ 2 * entropy ρ :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (by have := entropy_nonneg ρ hρ; positivity)).1 h
  linarith

theorem high_dim_entropy_eq_iff_written (d : ℕ) (hd : 12 ≤ d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  ((high_endpoint_written d hd).1 ρ hρ).2

theorem high_dim_beckner_onofri_written (d : ℕ) (hd : 12 ≤ d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  ⟨((high_endpoint_written d hd).2.1 u hu).1, ((high_endpoint_written d hd).2.1 u hu).2.1⟩

theorem high_dim_beckner_onofri_eq_iff_written (d : ℕ) (hd : 12 ≤ d) (u : Torus d → ℝ)
    (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  ((high_endpoint_written d hd).2.1 u hu).2.2

theorem high_dim_thresholds_written (d : ℕ) (hd : 12 ≤ d) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
      IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) ∧
      VariationalCurves.globalTransition d = spectralThreshold d ∧
      VariationalCurves.zeroDefectCoefficient d = spectralCoefficient d := by
  obtain ⟨-, -, hg, hgt, hA⟩ := high_endpoint_written d hd
  have hs : spectralThreshold d ≠ 0 := by
    have : (0 : ℝ) < spectralThreshold d := by
      unfold spectralThreshold
      have h2 : 0 < (d : ℝ) / 2 := by
        have : (12 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      exact div_pos (mul_pos two_pos (Real.rpow_pos_of_pos Real.pi_pos _))
        (Real.Gamma_pos_of_pos h2)
    exact this.ne'
  refine ⟨hg, hA, hgt, ?_⟩
  unfold VariationalCurves.zeroDefectCoefficient spectralCoefficient
  rw [hgt]
  field_simp

theorem high_dim_onset_branch_written (d : ℕ) (hd : 12 ≤ d) : FullBranchOnset d :=
  Onset.high_dim_onset_branch_of_inputs d hd (onsetEndpointInputs_written hd)

theorem high_dim_pressure_onset_written (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 :=
  Onset.high_dim_pressure_onset_of_inputs d hd (onsetEndpointInputs_written hd)

theorem high_dim_defect_onset_written (d : ℕ) (hd : 12 ≤ d) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 :=
  Onset.high_dim_defect_onset_of_inputs d hd (onsetEndpointInputs_written hd)

/-! ## Statement identity with `Final.Unconditional` -/

theorem onsetEndpointInputs_written_statement_eq :
    (type_of% @onsetEndpointInputs_written) = (type_of% @Final.Unconditional.onsetEndpointInputs) := rfl
theorem high_endpoint_written_statement_eq :
    (type_of% @high_endpoint_written) = (type_of% @Final.Unconditional.high_endpoint) := rfl
theorem high_dim_entropy_inequality_written_statement_eq :
    (type_of% @high_dim_entropy_inequality_written) =
      (type_of% @Final.Unconditional.high_dim_entropy_inequality) := rfl
theorem high_dim_entropy_eq_iff_written_statement_eq :
    (type_of% @high_dim_entropy_eq_iff_written) =
      (type_of% @Final.Unconditional.high_dim_entropy_eq_iff) := rfl
theorem high_dim_beckner_onofri_written_statement_eq :
    (type_of% @high_dim_beckner_onofri_written) =
      (type_of% @Final.Unconditional.high_dim_beckner_onofri) := rfl
theorem high_dim_beckner_onofri_eq_iff_written_statement_eq :
    (type_of% @high_dim_beckner_onofri_eq_iff_written) =
      (type_of% @Final.Unconditional.high_dim_beckner_onofri_eq_iff) := rfl
theorem high_dim_thresholds_written_statement_eq :
    (type_of% @high_dim_thresholds_written) = (type_of% @Final.Unconditional.high_dim_thresholds) := rfl
theorem high_dim_onset_branch_written_statement_eq :
    (type_of% @high_dim_onset_branch_written) =
      (type_of% @Final.Unconditional.high_dim_onset_branch) := rfl
theorem high_dim_pressure_onset_written_statement_eq :
    (type_of% @high_dim_pressure_onset_written) =
      (type_of% @Final.Unconditional.high_dim_pressure_onset) := rfl
theorem high_dim_defect_onset_written_statement_eq :
    (type_of% @high_dim_defect_onset_written) =
      (type_of% @Final.Unconditional.high_dim_defect_onset) := rfl

/-- Pointwise agreement with the existing final theorem (proof irrelevance). -/
theorem high_endpoint_written_eq (d : ℕ) (hd : 12 ≤ d) :
    high_endpoint_written d hd = Final.Unconditional.high_endpoint d hd := rfl

end BecknerOnofri.V2.Reaudit.SpinChannel
