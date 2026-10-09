module

public import BecknerOnofri.V2.Section3.Discharge
public import BecknerOnofri.V2.Section3.CircleCase
public import BecknerOnofri.VariationalExtendedConvexity

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

/-! ## The converse directions of the equality cases -/

theorem negSobolevEnergy_uniform (d : ℕ) : negSobolevEnergy (uniformDensity d).value = 0 := by
  unfold negSobolevEnergy
  refine ENNReal.tsum_eq_zero.mpr fun k => ?_
  have : fourierCoeff (uniformDensity d).value k.val = 0 := uniformDensity_fourierCoeff_nonzero _ k.property
  simp [this]

theorem torusEntropy_uniform (d : ℕ) : torusEntropy (uniformDensity d).value = 0 := by
  rw [torusEntropy_density_eq_ofReal_entropy _ (uniformDensity_finiteEntropy d),
    uniformDensity_entropy]
  simp

/-- A density that is a.e. `1` has equality in the entropy bound (both sides vanish). -/
theorem entropyEquality_of_uniform (ρ : ProbabilityDensity d)
    (h : ρ.value =ᵐ[torusMeasure d] fun _ => 1) : EntropyEquality d ρ := by
  have hu : ρ.value =ᵐ[torusMeasure d] (uniformDensity d).value := h
  unfold EntropyEquality
  rw [negSobolevEnergy_congr_ae hu, torusEntropy_congr_ae hu, negSobolevEnergy_uniform,
    torusEntropy_uniform]
  simp

/-- A critical Sobolev function that is a.e. constant has equality in the potential inequality. -/
theorem potential_equality_of_const (hd : 0 < d) (u : Torus d → ℝ) (hu : InCriticalSobolev u)
    (c : ℝ) (h : u =ᵐ[torusMeasure d] fun _ => c) :
    logPartition u = ((collapseCoefficient d * potentialEnergy u : ℝ) : EReal) := by
  have hf : ∀ k : NonzeroFrequency d, fourierCoeff u k.val = 0 := fun k => by
    rw [congrFun (BecknerOnofri.V2.Rearrangement.fourierCoeff_congr_ae' h) k.val]
    exact fourierCoeff_const_nonzero c k.property
  have hE : potentialEnergy u = 0 := by
    simp [potentialEnergy, potentialTerm, hf]
  have hmean : (∫ y, u y ∂torusMeasure d) = c := by
    rw [integral_congr_ae h]; simp
  have hcen : centered u =ᵐ[torusMeasure d] fun _ => (0 : ℝ) := by
    filter_upwards [h] with x hx
    simp [centered, hx, hmean]
  have hZ : (∫ x, Real.exp (centered u x) ∂torusMeasure d) = 1 := by
    rw [integral_congr_ae (by filter_upwards [hcen] with x hx; rw [hx])]
    simp
  rw [logPartition_eq_log_integral hd u hu, hZ, hE]
  simp

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

/-! ## Theorem 1.1 -/

/-- The entropy bound `eq:intro-low-dual`, on the whole of `𝒫_ac` (extended values: both sides in
`[0,∞]`; the right side is `⊤` for infinite entropy). -/
def ExtendedBound (d : ℕ) (ρ : ProbabilityDensity d) : Prop :=
  ENNReal.ofReal ((d : ℝ) * kernelConstant d) * negSobolevEnergy ρ.value ≤ torusEntropy ρ.value

theorem extendedBound_of_full (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ)
    (ρ : ProbabilityDensity d) : ExtendedBound d ρ := by
  by_cases hρ : ρ.FiniteEntropy
  · have hN : negSobolevEnergy ρ.value ≠ ∞ :=
      (negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ)
    have hc := kernelConstant_pos hd
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hb := hfull ρ hρ
    unfold EntropyBound at hb
    unfold ExtendedBound
    rw [← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_toReal ((torusEntropy_density_ne_top_iff ρ).2 hρ)]
    exact ENNReal.ofReal_le_ofReal hb
  · rw [ExtendedBound, torusEntropy_density_eq_top ρ hρ]
    exact le_top

/-- The coefficient `A_c(d)` is the least admissible coefficient (sharpness by concentration,
Lemma 2.3). -/
theorem collapse_isLeast (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) :
    IsLeast {A : ℝ | ∀ u : Torus d → ℝ, InCriticalSobolev u →
      logPartition u ≤ ((A * potentialEnergy u : ℝ) : EReal)} (collapseCoefficient d) := by
  refine ⟨fun u hu => (potential_bound_of_full hd hfull u hu).2, fun A hA => ?_⟩
  by_contra hlt
  have hlt := not_le.mp hlt
  have htop := coefficientDefect_below_collapse hd hlt
  have hle : coefficientDefect d A ≤ 0 := by
    unfold coefficientDefect
    refine iSup₂_le fun u hu => ?_
    have h := hA u hu
    rw [logPartition_eq_log_integral hd u hu] at h ⊢
    rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff]
    have h' := EReal.coe_le_coe_iff.mp h
    linarith
  rw [htop] at hle
  exact absurd hle (by simp)

/-- The pressure on the whole line: `P_d(β) = 0` for `β ≤ 2d` and `+∞` above. -/
theorem pressure_formula (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) (β : ℝ) :
    pressure d β = if β ≤ 2 * (d : ℝ) then 0 else ⊤ := by
  split_ifs with h
  · exact le_antisymm
      ((VariationalCurves.pressure_monotone hd h).trans
        (pressure_two_d_eq_zero_of_full hd hfull).le) (pressure_nonneg d β)
  · exact pressure_above_collapse hd (not_le.mp h)

/-- `β_gm(d) = 2d` (`= β_c(d)`). -/
theorem globalTransition_eq (hd : 0 < d)
    (hfull : ∀ σ : ProbabilityDensity d, σ.FiniteEntropy → EntropyBound d σ) :
    VariationalCurves.globalTransition d = 2 * (d : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine IsGreatest.csSup_eq ⟨⟨by positivity, pressure_two_d_eq_zero_of_full hd hfull⟩, ?_⟩
  rintro β ⟨-, hβ⟩
  by_contra hlt
  rw [pressure_above_collapse hd (not_le.mp hlt)] at hβ
  exact EReal.top_ne_zero hβ

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
