module

public import BecknerOnofri.V2.Eleven.UniformUnique
public import BecknerOnofri.V2.Eleven.PeriodizationSeries
public import BecknerOnofri.ElevenCoexistence
public import BecknerOnofri.ElevenUniformHessian
public import BecknerOnofri.ElevenPressureCorner
public import BecknerOnofri.ElevenDefectCorner
public import BecknerOnofri.ElevenDerivativeJumps
public import BecknerOnofri.RawEulerConvolution

@[expose] public section

/-! # Section 4, final assembly (G05): Lemma 4.8, Proposition 4.9, Proposition 4.1, Theorem 1.2

The logical order of the manuscript is kept:

1. the non-strict lower bound `3543/200 ≤ β_gm` and the uniqueness of the uniform minimizer on
   `[0, 3543/200]` (`UniformUnique.lean`);
2. the competitor bounds and the upper bound `β_gm < 2063/100 < β_s` (`Estimates.lean`);
3. local uniqueness (Lemma 4.8) and coexistence at `β_gm` (Proposition 4.9, existing module
   `ElevenCoexistence`, whose closure contains `transition_lower` (non-strict), `transition_upper`
   and `transition_pos`, and **not** `transition_strict_lower`/`transition_interval`: checked by
   `deptrace2.tsv`);
4. **only then** the strict lower bound `3543/200 < β_gm` (`strict_lower_of_coexistence`): a nonuniform
   global minimizer at `β_gm` contradicts the uniqueness of the uniform minimizer if `β_gm ≤ 3543/200`.

Route difference: Lemma 4.8 and Proposition 4.9 are the existing declarations (compactness and local
uniqueness are carried out in the repository's continuous-function framework, see `RESOLUTION.md`),
restated here in the manuscript's vocabulary. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Eleven

open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

/-! ## Lemma 4.8: local uniqueness -/

/-- `realGreen` has the Fourier coefficients of `g`: `ĝ(k) = 1/(β_s |k|^{11})` for `k ≠ 0`, `ĝ(0) = 0`
(`eq:section4-T-multipliers`; `endpointSigma 11 = spectralThreshold 11` definitionally). -/
theorem realGreen_fourier_multiplier (k : Frequency 11) :
    Legacy.TorusEndpoint.densityFourier (Legacy.TorusEndpoint.GreenKernelReal.realGreen 11) k =
      ((if k = 0 then 0 else 1 / (spectralThreshold 11 * frequencyLength k ^ 11) : ℝ) : ℂ) := by
  rw [Legacy.TorusEndpoint.GreenKernelReal.realGreen_fourierCoeff]
  congr 1

/-- **Lemma 4.8** (`lem:section4-local-uniqueness`): for `0 < β_0 < β_s` there are `ε > 0` (the open
interval `J = (β_0 - ε, β_0 + ε)`) and the neighborhood `U = {u ∈ H^{11}_0 : ‖u‖_{H^{11}} < ε}` of zero
such that for `β ∈ J` the only `u ∈ U` solving `u = β g * (e^u/∫e^u - 1)` (a.e.) is `u = 0`. -/
theorem local_uniqueness {β₀ : ℝ} (h0 : 0 < β₀) (hs : β₀ < spectralThreshold 11) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (β : ℝ) (u : Torus 11 → ℝ), |β - β₀| < ε → InSobolev 11 u → MeanZero u →
      sobolevNorm 11 u < ε →
      (u =ᵐ[torusMeasure 11] fun x => β * ∫ y,
        Legacy.TorusEndpoint.GreenKernelReal.realGreen 11 y * (normalizedGibbs u (x - y) - 1)
          ∂torusMeasure 11) →
      u =ᵐ[torusMeasure 11] fun _ => 0 := by
  obtain ⟨ε, hε, h⟩ := RawSubspectralLocalUniqueness.local_unique_convolution (d := 11)
    (by norm_num) h0 hs
  exact ⟨ε, hε, fun β u hβ hu hm hn he => h β u hβ (by simpa using hu) hm (by simpa using hn) he⟩

/-! ## Proposition 4.9: coexistence and corners -/

/-- The Section 4 statement of coexistence (`prop:section4-first-order-coexistence`), Hessian and
corners, in the vocabulary of `Statement.lean`.  Each component is the existing declaration (named). -/
theorem prop49 :
    -- (a) the uniform density and a nonuniform smooth strictly positive density minimize at `β_gm`
    (IsGlobalMinimizer (VariationalCurves.globalTransition 11) (uniformDensity 11) ∧
      ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer (VariationalCurves.globalTransition 11) ρ ∧
        SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
        ¬ ρ.value =ᵐ[torusMeasure 11] fun _ => 1) ∧
    -- (b) strictly positive Hessian at the uniform density (`eq:section4-uniform-strict-hessian`)
    (0 < 1 - VariationalCurves.globalTransition 11 / spectralThreshold 11 ∧
      ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
        (1 - VariationalCurves.globalTransition 11 / spectralThreshold 11) *
            ∫ x, h x ^ 2 ∂torusMeasure 11 ≤
          HighDim.Eleven.uniformHessian (VariationalCurves.globalTransition 11) h) ∧
    -- (c) corner of `P_11` at `β_gm` and of `C_11` at `A_gm`
    ((∀ β : ℝ, 0 < β → β < 22 → pressure 11 β = ↑(HighDim.Eleven.pressureReal β)) ∧
      ¬ DifferentiableAt ℝ HighDim.Eleven.pressureReal (VariationalCurves.globalTransition 11)) ∧
    ((∃ ε : ℝ, 0 < ε ∧ ε < VariationalCurves.zeroDefectCoefficient 11 ∧
        ∀ A : ℝ, |A - VariationalCurves.zeroDefectCoefficient 11| < ε →
          coefficientDefect 11 A = ↑(HighDim.Eleven.defectReal A)) ∧
      ¬ DifferentiableAt ℝ HighDim.Eleven.defectReal (VariationalCurves.zeroDefectCoefficient 11)) ∧
    -- (d) one-sided derivatives (`eq:section4-pressure-derivative-jump`, `eq:section4-defect-derivative-jump`)
    (∃ p : ℝ, 0 < p ∧
      HasDerivWithinAt HighDim.Eleven.pressureReal 0 (Set.Iio (VariationalCurves.globalTransition 11))
        (VariationalCurves.globalTransition 11) ∧
      HasDerivWithinAt HighDim.Eleven.pressureReal p (Set.Ioi (VariationalCurves.globalTransition 11))
        (VariationalCurves.globalTransition 11)) ∧
    (∃ q : ℝ, q < 0 ∧
      HasDerivWithinAt HighDim.Eleven.defectReal q (Set.Iio (VariationalCurves.zeroDefectCoefficient 11))
        (VariationalCurves.zeroDefectCoefficient 11) ∧
      HasDerivWithinAt HighDim.Eleven.defectReal 0 (Set.Ioi (VariationalCurves.zeroDefectCoefficient 11))
        (VariationalCurves.zeroDefectCoefficient 11)) :=
  ⟨HighDim.Eleven.coexistence, HighDim.Eleven.uniform_hessian, HighDim.Eleven.pressure_corner,
    HighDim.Eleven.defect_corner, HighDim.Eleven.pressure_derivative_jump,
    HighDim.Eleven.defect_derivative_jump⟩

/-! ## Proposition 4.1 and the strict lower bound (only after coexistence) -/

/-- The strict lower bound `3543/200 < β_gm(11)`: the non-strict bound (`UniformUnique`), the
nonuniform global minimizer at `β_gm` (`prop49`), and the uniqueness of the uniform minimizer
at every `β ≤ 3543/200`. -/
theorem strict_lower_of_coexistence : beta0 < VariationalCurves.globalTransition 11 := by
  refine lt_of_le_of_ne transition_lower fun heq => ?_
  obtain ⟨-, ρ, hmin, -, -, hnon⟩ := prop49.1
  have hβ0 : (0 : ℝ) ≤ VariationalCurves.globalTransition 11 := by
    rw [← heq]; unfold beta0; norm_num
  exact hnon ((uniform_unique _ hβ0 heq.ge ρ hmin.1).1 hmin)

/-- **Proposition 4.1** (`d11:thm:interval`). -/
theorem prop41 :
    (3543 / 200 < VariationalCurves.globalTransition 11 ∧
      VariationalCurves.globalTransition 11 < 2063 / 100) ∧
    (∀ β : ℝ, 0 ≤ β → β ≤ 3543 / 200 → ∀ ρ : ProbabilityDensity 11, ρ.FiniteEntropy →
      (IsGlobalMinimizer β ρ ↔ ρ.value =ᵐ[torusMeasure 11] fun _ => 1)) ∧
    (∀ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile →
      (14475384292906 : ℝ) / 10 ^ 12 <
        (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy ρ.value).toReal) := by
  have hρ : ∃ ρ : ProbabilityDensity 11, ρ.value = HighDim.Eleven.periodizedProfile :=
    ⟨HighDim.Eleven.competitorDensity, rfl⟩
  obtain ⟨ρ₀, hρ₀⟩ := hρ
  refine ⟨⟨?_, transition_upper ρ₀ hρ₀⟩, fun β hβ hβ0 ρ hρ => uniform_unique β hβ hβ0 ρ hρ,
    fun ρ h => periodized_energy_bound ρ h⟩
  exact strict_lower_of_coexistence

/-- The density `ρ_*` as a `ProbabilityDensity 11`. -/
def rhoStar : ProbabilityDensity 11 := HighDim.Eleven.competitorDensity

theorem rhoStar_value : rhoStar.value = HighDim.Eleven.periodizedProfile := rfl

/-- **Theorem 1.2** (`thm:intro-d11`). -/
theorem theorem_1_2 :
    -- `ρ_*` is a smooth, strictly positive probability density, with the two certificates
    (rhoStar.value = HighDim.Eleven.periodizedProfile ∧ rhoStar.FiniteEntropy ∧
      SmoothOnTorus rhoStar.value ∧ (∀ x, 0 < rhoStar.value x) ∧
      (torusEntropy rhoStar.value).toReal < 8653 / 600 ∧
      (14475384292906 : ℝ) / 10 ^ 12 <
        (2 * Real.pi) ^ 11 / 2 * (negSobolevEnergy rhoStar.value).toReal) ∧
    -- `C_11(A_s) = P_11(β_s) > 1/30`
    (coefficientDefect 11 (spectralCoefficient 11) = pressure 11 (spectralThreshold 11) ∧
      (((1 : ℝ) / 30 : ℝ) : EReal) < pressure 11 (spectralThreshold 11)) ∧
    -- `17.715 < β_gm < 20.630 < β_s < 22`
    (3543 / 200 < VariationalCurves.globalTransition 11 ∧
      VariationalCurves.globalTransition 11 < 2063 / 100 ∧ 2063 / 100 < spectralThreshold 11 ∧
      spectralThreshold 11 < 22) ∧
    -- coexistence, positive Hessian, corners
    (IsGlobalMinimizer (VariationalCurves.globalTransition 11) (uniformDensity 11) ∧
      ∃ ρ : ProbabilityDensity 11, IsGlobalMinimizer (VariationalCurves.globalTransition 11) ρ ∧
        SmoothOnTorus ρ.value ∧ (∀ x, 0 < ρ.value x) ∧
        ¬ ρ.value =ᵐ[torusMeasure 11] fun _ => 1) ∧
    (0 < 1 - VariationalCurves.globalTransition 11 / spectralThreshold 11 ∧
      ∀ h : Torus 11 → ℝ, SmoothOnTorus h → MeanZero h →
        (1 - VariationalCurves.globalTransition 11 / spectralThreshold 11) *
            ∫ x, h x ^ 2 ∂torusMeasure 11 ≤
          HighDim.Eleven.uniformHessian (VariationalCurves.globalTransition 11) h) ∧
    ¬ DifferentiableAt ℝ HighDim.Eleven.pressureReal (VariationalCurves.globalTransition 11) ∧
    ¬ DifferentiableAt ℝ HighDim.Eleven.defectReal (VariationalCurves.zeroDefectCoefficient 11) := by
  have hv := prop41
  have h49 := prop49
  have hsm : SmoothOnTorus rhoStar.value := periodizedProfile_smooth_of_M_test
  refine ⟨⟨rhoStar_value, finiteEntropy_of_value_eq _ rhoStar_value, hsm,
      fun x => HighDim.Eleven.periodizedProfile_pos x, periodized_entropy_bound _ rhoStar_value,
      periodized_energy_bound _ rhoStar_value⟩,
    ⟨defect_spectral_eq_pressure, spectral_pressure_gt_thirtieth _ rhoStar_value⟩,
    ⟨hv.1.1, hv.1.2, upper_lt_spectral.1, upper_lt_spectral.2⟩, h49.1, h49.2.1,
    h49.2.2.1.2, h49.2.2.2.1.2⟩

end BecknerOnofri.V2.Eleven
