module

public import BecknerOnofri.V2.Vocab.Section2Bridge
public import BecknerOnofri.HeatEntropyConvergence
public import BecknerOnofri.HeatRegularization

@[expose] public section

/-! # Lemma 2.1, heat approximation: filter `t ↓ 0` versions in the manuscript normalization (G02)

The repository proves `heat_entropy_tendsto` and `heatRegularization_interaction_limit` along
sequences `t_n ↓ 0`.  Here:

* `tendsto_nhdsGT_of_seq`: sequence-to-filter principle for the filter `𝓝[>] 0`;
* `heat_entropy_tendsto_nhdsGT`: `Ent(ρ_t) → Ent(ρ)` (`eq:section2-entropy-heat-approximation`)
  both for the real integral `∫ ρ_t log ρ_t` and for the homogeneous entropy `torusEntropy`;
* `heat_negSobolevEnergy_tendsto_nhdsGT`: `‖ρ_t‖²_{Ḣ^{-d/2}} → ‖ρ‖²_{Ḣ^{-d/2}}`
  (`eq:section2-energy-heat-approximation`), in `ℝ≥0∞`, and `c_d‖ρ_t‖² → c_d‖ρ‖²` in `ℝ`.

Here `ρ_t = heatRegularization ρ t` has multiplier `e^{-4π²|k|²t}`, exactly the manuscript's `P_t`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Vocab
open BecknerOnofri.HighDim

/-- A function tends to `L` along `𝓝[>] 0` as soon as it does along every positive sequence
tending to `0`. -/
theorem tendsto_nhdsGT_of_seq {X : Type*} [TopologicalSpace X] {f : ℝ → X} {L : X}
    (h : ∀ u : ℕ → ℝ, (∀ n, 0 < u n) → Tendsto u atTop (𝓝 0) →
      Tendsto (fun n => f (u n)) atTop (𝓝 L)) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  refine tendsto_of_seq_tendsto fun u hu => ?_
  have hpos : ∀ᶠ n in atTop, 0 < u n := hu.eventually self_mem_nhdsWithin
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have hu' : Tendsto (fun n => u (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    hu.comp (tendsto_add_atTop_nat N)
  have h0 : Tendsto (fun n => u (n + N)) atTop (𝓝 0) := (tendsto_nhdsWithin_iff.1 hu').1
  have := h (fun n => u (n + N)) (fun n => hN _ (by omega)) h0
  exact (tendsto_add_atTop_iff_nat (f := fun n => f (u n)) N).1 this

section HeatDensity
variable {d : ℕ}

/-- For `t > 0` the heat regularization is a finite-entropy density. -/
theorem heatRegularization_finiteEntropy_density (ρ : ProbabilityDensity d) {t : ℝ}
    (ht : 0 < t) : ∃ η : ProbabilityDensity d, η.value = heatRegularization ρ t ∧
      η.FiniteEntropy := by
  obtain ⟨η, h1, h2, -, -⟩ := heatRegularization_regular ρ ht
  exact ⟨η, h1, h2⟩

/-- `Ent(ρ_t)` as the homogeneous entropy is the real integral `∫ ρ_t log ρ_t`. -/
theorem torusEntropy_heatRegularization (ρ : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    torusEntropy (heatRegularization ρ t) =
      ENNReal.ofReal (∫ x, heatRegularization ρ t x * Real.log (heatRegularization ρ t x)
        ∂torusMeasure d) := by
  obtain ⟨η, h1, h2⟩ := heatRegularization_finiteEntropy_density ρ ht
  have := torusEntropy_density_eq_ofReal_entropy η h2
  rw [h1] at this
  unfold entropy at this
  rw [h1] at this
  exact this

/-- **`eq:section2-entropy-heat-approximation`, real form, filter `t ↓ 0`.** -/
theorem heat_entropy_integral_tendsto_nhdsGT (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Tendsto (fun t : ℝ => ∫ x, heatRegularization ρ t x * Real.log (heatRegularization ρ t x)
      ∂torusMeasure d) (𝓝[>] (0 : ℝ)) (𝓝 (entropy ρ)) :=
  tendsto_nhdsGT_of_seq fun u hu hu0 => HeatApproximation.heat_entropy_tendsto ρ hρ u hu hu0

/-- **`eq:section2-entropy-heat-approximation`, filter `t ↓ 0`, homogeneous entropy.**
`Ent(ρ_t) → Ent(ρ)` in `ℝ≥0∞` (all terms finite). -/
theorem heat_entropy_tendsto_nhdsGT (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    Tendsto (fun t : ℝ => torusEntropy (heatRegularization ρ t)) (𝓝[>] (0 : ℝ))
      (𝓝 (torusEntropy ρ.value)) := by
  rw [torusEntropy_density_eq_ofReal_entropy ρ hρ]
  have h := (ENNReal.tendsto_ofReal (heat_entropy_integral_tendsto_nhdsGT ρ hρ))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (torusEntropy_heatRegularization ρ ht).symm

/-- The energy of `ρ_t` is finite (`ρ_t` has finite entropy). -/
theorem negSobolevEnergy_heatRegularization_ne_top (hd : 0 < d) (ρ : ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) : negSobolevEnergy (heatRegularization ρ t) ≠ ∞ := by
  obtain ⟨η, h1, h2⟩ := heatRegularization_finiteEntropy_density ρ ht
  rw [← h1]
  exact (negSobolevEnergy_ne_top_iff η).2 (finiteEntropy_spectralEnergy_ne_top hd η h2)

/-- The Green double integral of `ρ_t` is `c_d ‖ρ_t‖²_{Ḣ^{-d/2}}`. -/
theorem heat_green_interaction_eq (hd : 0 < d) (ρ : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) *
        heatRegularization ρ t x * heatRegularization ρ t y ∂torusMeasure d ∂torusMeasure d) =
      kernelConstant d * (negSobolevEnergy (heatRegularization ρ t)).toReal := by
  obtain ⟨η, h1, h2⟩ := heatRegularization_finiteEntropy_density ρ ht
  have := green_interaction_eq_kernelConstant_mul hd η h2
  rw [h1] at this
  exact this

/-- Filter version of `heatRegularization_interaction_limit`. -/
theorem heat_interaction_tendsto_nhdsGT (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    Tendsto (fun t : ℝ => ∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) *
        heatRegularization ρ t x * heatRegularization ρ t y ∂torusMeasure d ∂torusMeasure d)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x, ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d (x - y) *
        ρ.value x * ρ.value y ∂torusMeasure d ∂torusMeasure d)) :=
  tendsto_nhdsGT_of_seq fun u hu hu0 => heatRegularization_interaction_limit hd ρ hρ u hu hu0

/-- **`eq:section2-energy-heat-approximation`, real form:**
`c_d ‖ρ_t‖²_{Ḣ^{-d/2}} → c_d ‖ρ‖²_{Ḣ^{-d/2}}` as `t ↓ 0`. -/
theorem heat_energy_real_tendsto_nhdsGT (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    Tendsto (fun t : ℝ => kernelConstant d * (negSobolevEnergy (heatRegularization ρ t)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (kernelConstant d * (negSobolevEnergy ρ.value).toReal)) := by
  rw [← green_interaction_eq_kernelConstant_mul hd ρ hρ]
  refine (heat_interaction_tendsto_nhdsGT hd ρ hρ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact heat_green_interaction_eq hd ρ ht

/-- **`eq:section2-energy-heat-approximation`.**
`‖ρ_t‖²_{Ḣ^{-d/2}} → ‖ρ‖²_{Ḣ^{-d/2}}` in `ℝ≥0∞` as `t ↓ 0` (finite entropy). -/
theorem heat_negSobolevEnergy_tendsto_nhdsGT (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    Tendsto (fun t : ℝ => negSobolevEnergy (heatRegularization ρ t)) (𝓝[>] (0 : ℝ))
      (𝓝 (negSobolevEnergy ρ.value)) := by
  have hc := kernelConstant_pos hd
  have h := (heat_energy_real_tendsto_nhdsGT hd ρ hρ).const_mul (kernelConstant d)⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h
  have hfin : negSobolevEnergy ρ.value ≠ ∞ :=
    (negSobolevEnergy_ne_top_iff ρ).2 (finiteEntropy_spectralEnergy_ne_top hd ρ hρ)
  rw [← ENNReal.ofReal_toReal hfin]
  refine (ENNReal.tendsto_ofReal h).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ENNReal.ofReal_toReal (negSobolevEnergy_heatRegularization_ne_top hd ρ ht)

end HeatDensity

end BecknerOnofri.V2.Vocab
