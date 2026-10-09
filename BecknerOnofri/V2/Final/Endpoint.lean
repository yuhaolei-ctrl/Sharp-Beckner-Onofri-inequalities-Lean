module

public import BecknerOnofri.V2.Final.Scalar
public import BecknerOnofri.V2.Assembly.All
public import BecknerOnofri.V2.Onset.Inputs
public import BecknerOnofri.V2.Onset.Theorem13
public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import BecknerOnofri.Kappa

@[expose] public section

/-! # Dimensions `d ≥ 12`: endpoint and onset from the three finite checks (Final package)

* `onsetEndpointInputs_of_scalarBounds` discharges `Onset.OnsetEndpointInputs d` (the spectral
  inequality of Corollary 5.8 and the forward direction of its equality case) for every `d ≥ 12` from
  `Assembly.ScalarBounds` through `Assembly.spectral_high_density` (itself `Transfer.spectral_dimension_transfer`
  applied to `Assembly.spectralD12Inequality` and `Assembly.spectralD12Equality`).  No bridge is missing:
  `SpectralEndpointInequality d` is literally the first conjunct and `DensityRigidityForward d` the
  forward direction of the second conjunct of `spectral_high_density`.
* The statements of `Challenge.lean` for `d ≥ 12` (Theorem 1.3), with the only hypotheses `hd : 12 ≤ d`
  and the three finite interval checks `hc1 hc2 hc3`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Final
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab BecknerOnofri.V2.Interval

/-! ## The onset inputs -/

theorem onsetEndpointInputs_of_scalarBounds (hsc : Assembly.ScalarBounds) {d : ℕ} (hd : 12 ≤ d) :
    Onset.OnsetEndpointInputs d :=
  ⟨fun ρ hρ => (Assembly.spectral_high_density hsc hd ρ hρ).1,
    fun ρ hρ h => ((Assembly.spectral_high_density hsc hd ρ hρ).2).mp h⟩

theorem onsetEndpointInputs_of_checks
    (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) {d : ℕ} (hd : 12 ≤ d) :
    Onset.OnsetEndpointInputs d :=
  onsetEndpointInputs_of_scalarBounds (scalarBounds_of_checks hc1 hc2 hc3) hd

/-! ## An `EReal` form of the entropy inequalities -/

/-- If `c · (spectralEnergy ρ).toReal ≤ Ent ρ` for finite-entropy `ρ` (and `0 < d`), then
`c · spectralEnergy ρ ≤ extendedEntropy ρ` in `EReal`, with `Ent = ∞` allowed. -/
theorem ereal_le_extendedEntropy {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d) (c : ℝ)
    (h : ρ.FiniteEntropy → c * (spectralEnergy ρ).toReal ≤ entropy ρ) :
    (c : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ := by
  by_cases hρ : ρ.FiniteEntropy
  · have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top hd ρ hρ
    rw [extendedEntropy_eq_torusEntropy, torusEntropy_density_eq_ofReal_entropy ρ hρ,
      EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg ρ hρ),
      ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact h hρ
  · rw [extendedEntropy_eq_torusEntropy, torusEntropy_density_eq_top ρ hρ]
    exact le_top

/-! ## Theorem 1.3 (`d ≥ 12`), statements of `Challenge.lean` -/

section Endpoint
variable (d : ℕ)

/-- **Theorem 1.3, (eq:intro-high-dual).**  Statement as in `Challenge.high_dim_entropy_inequality`. -/
theorem high_dim_entropy_inequality_of_scalarBounds (hd : 12 ≤ d) (hsc : Assembly.ScalarBounds)
    (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ := by
  refine ereal_le_extendedEntropy (by omega) ρ _ fun hρ => ?_
  have h := (Assembly.spectral_high_density hsc hd ρ hρ).1
  have hfin : spectralEnergy ρ ≠ ⊤ := finiteEntropy_spectralEnergy_ne_top (by omega) ρ hρ
  have h2 : (spectralEnergy ρ).toReal ≤ 2 * entropy ρ :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (by have := entropy_nonneg ρ hρ; positivity)).1 h
  linarith

/-- **Theorem 1.3, equality in (eq:intro-high-dual).**  Statement as in
`Challenge.high_dim_entropy_eq_iff`. -/
theorem high_dim_entropy_eq_iff_of_scalarBounds (hd : 12 ≤ d) (hsc : Assembly.ScalarBounds)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  (Assembly.high_endpoint hsc hd).1 ρ hρ |>.2

/-- **Theorem 1.3, (eq:intro-high-primal).**  Statement as in `Challenge.high_dim_beckner_onofri`. -/
theorem high_dim_beckner_onofri_of_scalarBounds (hd : 12 ≤ d) (hsc : Assembly.ScalarBounds)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  ⟨((Assembly.high_endpoint hsc hd).2.1 u hu).1, ((Assembly.high_endpoint hsc hd).2.1 u hu).2.1⟩

/-- **Theorem 1.3, equality in (eq:intro-high-primal).**  Statement as in
`Challenge.high_dim_beckner_onofri_eq_iff`. -/
theorem high_dim_beckner_onofri_eq_iff_of_scalarBounds (hd : 12 ≤ d) (hsc : Assembly.ScalarBounds)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  ((Assembly.high_endpoint hsc hd).2.1 u hu).2.2

/-- **Theorem 1.3, (eq:intro-high-threshold).**  Statement as in `Challenge.high_dim_thresholds`. -/
theorem high_dim_thresholds_of_scalarBounds (hd : 12 ≤ d) (hsc : Assembly.ScalarBounds) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
      IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) ∧
      VariationalCurves.globalTransition d = spectralThreshold d ∧
      VariationalCurves.zeroDefectCoefficient d = spectralCoefficient d := by
  obtain ⟨-, -, hg, hgt, hA⟩ := Assembly.high_endpoint hsc hd
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

/-- **(eq:intro-kappa).**  Statement as in `Challenge.kappa_pos` (an elementary inequality; no
dependence on `ScalarBounds`). -/
theorem kappa_pos (hd : 12 ≤ d) : 0 < kappa d := HighDim.kappa_pos d hd


/-- `Assembly.high_endpoint` (Corollary 5.8) from the three finite checks. -/
theorem high_endpoint_of_checks
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
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
  Assembly.high_endpoint (scalarBounds_of_checks hc1 hc2 hc3) hd

theorem high_dim_entropy_inequality
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true)
    (ρ : ProbabilityDensity d) :
    ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ :=
  high_dim_entropy_inequality_of_scalarBounds d hd (scalarBounds_of_checks hc1 hc2 hc3) ρ

theorem high_dim_entropy_eq_iff
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
      ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  high_dim_entropy_eq_iff_of_scalarBounds d hd (scalarBounds_of_checks hc1 hc2 hc3) ρ hρ

theorem high_dim_beckner_onofri
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
      logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) :=
  high_dim_beckner_onofri_of_scalarBounds d hd (scalarBounds_of_checks hc1 hc2 hc3) u hu

theorem high_dim_beckner_onofri_eq_iff
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) :
    logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c :=
  high_dim_beckner_onofri_eq_iff_of_scalarBounds d hd (scalarBounds_of_checks hc1 hc2 hc3) u hu

theorem high_dim_thresholds
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
      IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) ∧
      VariationalCurves.globalTransition d = spectralThreshold d ∧
      VariationalCurves.zeroDefectCoefficient d = spectralCoefficient d :=
  high_dim_thresholds_of_scalarBounds d hd (scalarBounds_of_checks hc1 hc2 hc3)

end Endpoint

section Onset
variable (d : ℕ)

/-- **Theorem 1.3, (eq:intro-onset-range)–(eq:intro-onset-branch).**  Statement as in
`Challenge.high_dim_onset_branch`; the only hypotheses are the three finite checks. -/
theorem high_dim_onset_branch
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    FullBranchOnset d :=
  Onset.high_dim_onset_branch_of_inputs d hd (onsetEndpointInputs_of_checks hc1 hc2 hc3 hd)

/-- **Theorem 1.3, (eq:intro-pressure-onset).**  Statement as in `Challenge.high_dim_pressure_onset`. -/
theorem high_dim_pressure_onset
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3 :=
  Onset.high_dim_pressure_onset_of_inputs d hd (onsetEndpointInputs_of_checks hc1 hc2 hc3 hd)

/-- **Theorem 1.3, (eq:intro-C-onset).**  Statement as in `Challenge.high_dim_defect_onset`. -/
theorem high_dim_defect_onset
    (hd : 12 ≤ d) (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 :=
  Onset.high_dim_defect_onset_of_inputs d hd (onsetEndpointInputs_of_checks hc1 hc2 hc3 hd)

end Onset

#print axioms onsetEndpointInputs_of_checks
#print axioms high_endpoint_of_checks
#print axioms high_dim_entropy_inequality
#print axioms high_dim_entropy_eq_iff
#print axioms high_dim_beckner_onofri
#print axioms high_dim_beckner_onofri_eq_iff
#print axioms high_dim_thresholds
#print axioms kappa_pos
#print axioms high_dim_onset_branch
#print axioms high_dim_pressure_onset
#print axioms high_dim_defect_onset

end BecknerOnofri.V2.Final
