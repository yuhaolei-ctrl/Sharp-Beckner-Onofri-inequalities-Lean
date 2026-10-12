module

public import BecknerOnofri.V2.Reaudit.Final.All

@[expose] public section

/-! # Theorems 1.1 and 1.3 as printed (Reaudit, Final)

Each theorem below states, as one conjunction, every assertion of the corresponding printed theorem of
the manuscript (SHA-256 1a3b8bdb...), and is proved from the route-aligned declarations.  The
Challenge-shaped regression targets are unchanged; these are added next to them.  Theorem 1.2 is
`Final.theorem_1_2_route` (statement `V2.Eleven.theorem_1_2`, both printed constants) together with
`eleven_competitor_printed`. -/

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
  ⟨fun ρ => SpinChannel.high_dim_entropy_inequality_written d hd ρ,
    fun ρ hρ => SpinChannel.high_dim_entropy_eq_iff_written d hd ρ hρ,
    fun u hu => SpinChannel.high_dim_beckner_onofri_written d hd u hu,
    fun u hu => SpinChannel.high_dim_beckner_onofri_eq_iff_written d hd u hu,
    SpinChannel.high_dim_thresholds_written d hd,
    V2.Final.kappa_pos d hd,
    Onset.high_dim_onset_branch_route d hd,
    Onset.high_dim_pressure_onset_route d hd,
    Onset.high_dim_defect_onset_route d hd,
    Onset.onset_manuscript d hd⟩


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
#print axioms theorem_1_3_printed

end V2.Reaudit.Final
end BecknerOnofri

end
