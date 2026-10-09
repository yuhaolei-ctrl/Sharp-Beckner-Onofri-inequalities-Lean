module

public import BecknerOnofri.V2.Section3.FinalCore
public import BecknerOnofri.V2.Section3.Written

@[expose] public section

/-! # Proposition 3.7 and Theorem 1.1 through the written route (G04)

`theorem_1_1_written` has the same statement as `theorem_1_1` (`Final.lean`), but its hypothesis
`EntropyBound d ρ` for `2 ≤ d ≤ 10` comes from `lemma_3_1` applied to `mixtureInequality_written` and
`mixtureStrictness_written`, i.e. the manuscript's literal class (all finite-entropy countable
cosine-power mixtures) and the manuscript's argument (Lemma 3.3, Proposition 3.4, Lemma 3.5, the
chain rule and Lemma 3.2).  This module imports neither `Discharge` nor any module of the legacy
chain `Legacy.BecknerOnofri.LowDimensionMixtureEndpoint`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- The written mixture statements imply the smooth ones used by the legacy-route discharge. -/
theorem written_implies_smooth (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    SmoothMixtureInequality d ∧ SmoothMixtureStrictness d :=
  ⟨(mixtureInequality_written hd2 hd10).toSmooth, (mixtureStrictness_written hd2 hd10).toSmooth⟩

/-- **Proposition 3.7 (`prop:equality`)**, written route. -/
theorem prop_3_7_written (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (EntropyEquality d ρ ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) := by
  obtain ⟨-, hdens, -, -, hpot⟩ :=
    lemma_3_1 hd2 (mixtureInequality_written hd2 hd10) (mixtureStrictness_written hd2 hd10)
  exact ⟨fun ρ hρ => ⟨hdens ρ hρ, entropyEquality_of_uniform ρ⟩,
    fun u hu => ⟨hpot u hu, fun ⟨c, hc⟩ => potential_equality_of_const (by omega) u hu c hc⟩⟩

/-- **Theorem 1.1 (`thm:intro-low-dimensional`), `1 ≤ d ≤ 10`**, through the written route; same
statement as `theorem_1_1`. -/
theorem theorem_1_1_written (hd1 : 1 ≤ d) (hd10 : d ≤ 10) :
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal)) ∧
    (∀ ρ : ProbabilityDensity d, ExtendedBound d ρ) ∧
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) ∧
    (d = 1 →
      (∀ ρ : ProbabilityDensity 1, ρ.FiniteEntropy →
        (EntropyEquality 1 ρ ↔ ∃ a : ℂ, ‖a‖ < 1 ∧ ρ.value =ᵐ[torusMeasure 1]
          fun x => (1 - ‖a‖ ^ 2) / ‖fourier 1 (x 0) - a‖ ^ 2)) ∧
      (∀ u : Torus 1 → ℝ, InCriticalSobolev u →
        (logPartition u = ((collapseCoefficient 1 * potentialEnergy u : ℝ) : EReal) ↔
          ∃ a : ℂ, ‖a‖ < 1 ∧ ∃ c : ℝ, u =ᵐ[torusMeasure 1]
            fun x => -2 * Real.log ‖1 - conj a * fourier 1 (x 0)‖ + c))) ∧
    (2 ≤ d →
      (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
        (EntropyEquality d ρ ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
      (∀ u : Torus d → ℝ, InCriticalSobolev u →
        (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c))) ∧
    coefficientDefect d (collapseCoefficient d) = 0 ∧
    (∀ β : ℝ, pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤) ∧
    VariationalCurves.globalTransition d = 2 * (d : ℝ) := by
  have hd0 : 0 < d := by omega
  have hfull : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → EntropyBound d ρ := by
    rcases Nat.eq_or_lt_of_le hd1 with h | h
    · subst h; exact fun ρ hρ => circle_entropy_bound ρ hρ
    · exact (lemma_3_1 (by omega) (mixtureInequality_written (by omega) hd10)
        (mixtureStrictness_written (by omega) hd10)).1
  refine ⟨fun u hu => potential_bound_of_full hd0 hfull u hu,
    fun ρ => extendedBound_of_full hd0 hfull ρ, collapse_isLeast hd0 hfull, ?_, ?_,
    coefficientDefect_collapse_eq_zero_of_full hd0 hfull, pressure_formula hd0 hfull,
    globalTransition_eq hd0 hfull⟩
  · rintro rfl
    exact ⟨fun ρ hρ => circle_entropy_equality_iff ρ hρ,
      fun u hu => circle_potential_equality_iff u hu⟩
  · intro h2
    exact prop_3_7_written h2 hd10

#print axioms written_implies_smooth
#print axioms prop_3_7_written
#print axioms theorem_1_1_written

end BecknerOnofri.V2.Section3
