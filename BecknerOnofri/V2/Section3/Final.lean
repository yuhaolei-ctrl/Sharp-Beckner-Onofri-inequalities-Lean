module

public import BecknerOnofri.V2.Section3.Discharge
public import BecknerOnofri.V2.Section3.FinalCore

@[expose] public section

/-! # Proposition 3.7 (`prop:equality`) and the proof of Theorem 1.1 (G04)

* `prop_3_7`: for `2 ≤ d ≤ 10`, equality in `eq:collapse-entropy-full` holds only for the uniform
  density and equality in the dual potential inequality holds only for constants (and conversely).
  The proof is `lemma_3_1_smooth` with its two hypotheses discharged by `mixtureInequality_smooth`
  and `mixtureStrictness_smooth` (the mixture/scalar route), **not** by `Target.low_density_rigidity`
  or `endpoint_through_ten`.
* `theorem_1_1`: Theorem 1.1 (`thm:intro-low-dimensional`), `1 ≤ d ≤ 10`.  The case `d = 1` goes through
  the circle results of `CircleCase.lean` (Lebedev--Milin, Poisson kernels, conformal potentials), and
  no rigidity conclusion of `d ≥ 2` is stated for `d = 1`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-! ## Proposition 3.7 -/

/-- **Proposition 3.7 (`prop:equality`).**  For `2 ≤ d ≤ 10`: equality in `eq:collapse-entropy-full`
holds exactly for the uniform density, and equality in the dual potential inequality holds exactly
for constants. -/
theorem prop_3_7 (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (EntropyEquality d ρ ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      (logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
        ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) := by
  obtain ⟨-, hdens, -, -, hpot⟩ :=
    lemma_3_1_smooth (by omega) (mixtureInequality_smooth hd2 hd10)
      (mixtureStrictness_smooth hd2 hd10)
  exact ⟨fun ρ hρ => ⟨hdens ρ hρ, entropyEquality_of_uniform ρ⟩,
    fun u hu => ⟨hpot u hu, fun ⟨c, hc⟩ => potential_equality_of_const (by omega) u hu c hc⟩⟩


/-- **Theorem 1.1 (`thm:intro-low-dimensional`), `1 ≤ d ≤ 10`.**

1. the potential inequality `log ∫ e^{u-ū} ≤ A_c(d) ‖u‖²_{Ḣ^{d/2}}` on `H^{d/2}`;
2. the entropy bound `Ent ρ ≥ d c_d ‖ρ‖²_{Ḣ^{-d/2}}` on all of `𝒫_ac` (extended values);
3. sharpness of the coefficient;
4. equality: for `d = 1` exactly the Poisson kernels, resp. the logarithms of Poisson kernels (a
   nonconstant family); for `2 ≤ d ≤ 10` exactly the uniform density, resp. constants;
5. `C_d(A_c) = 0`, `P_d(β) = 0` for `β ≤ 2d` and `⊤` above, `β_gm(d) = 2d`. -/
theorem theorem_1_1 (hd1 : 1 ≤ d) (hd10 : d ≤ 10) :
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
    · exact (lemma_3_1_smooth hd0 (mixtureInequality_smooth (by omega) hd10)
        (mixtureStrictness_smooth (by omega) hd10)).1
  refine ⟨fun u hu => potential_bound_of_full hd0 hfull u hu,
    fun ρ => extendedBound_of_full hd0 hfull ρ, collapse_isLeast hd0 hfull, ?_, ?_,
    coefficientDefect_collapse_eq_zero_of_full hd0 hfull, pressure_formula hd0 hfull,
    globalTransition_eq hd0 hfull⟩
  · rintro rfl
    exact ⟨fun ρ hρ => circle_entropy_equality_iff ρ hρ,
      fun u hu => circle_potential_equality_iff u hu⟩
  · intro h2
    exact prop_3_7 h2 hd10

#print axioms prop_3_7
#print axioms theorem_1_1

end BecknerOnofri.V2.Section3
