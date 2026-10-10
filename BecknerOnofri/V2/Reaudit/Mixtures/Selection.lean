module

public import BecknerOnofri.V2.Rearrangement.Comparison
public import BecknerOnofri.GeneralEuler.Paper
public import BecknerOnofri.CanonicalSelectionDefinitions
public import BecknerOnofri.CanonicalSelectionFourier
public import BecknerOnofri.SmoothTorusSobolev

@[expose] public section

/-! # Lemma 2.13 `lem:selection-full-entropy-domain` through the written-route wrapper (S016)

The printed proof of the entropy-preserving selection is

* (i) attainment and smoothness/positivity of minimizers (`OptimizerDuality.exists_minimizer`,
  `minimizer_smooth_positive_kirkwood`);
* (ii) apply the successive coordinate rearrangements `eq:rearrangement` to a minimizer: they preserve
  entropy and do not decrease `‖ρ‖²_{Ḣ^{-d/2}}`, so `ρ⋆` is again a minimizer, with Gibbs form and
  smooth Euler pair; this is **`Rearrangement.coordinate_rearranged_minimizer`** (the written
  energy comparison of Lemma 2.9: `rearranged_pressureValue_ge`);
* (iii) Proposition 2.12 gives the mixture representation: **`GeneralEulerBridge.cosine_representation`**;
  the sign of the Fourier coefficients follows from the Euler relation; entropy preservation preserves
  nonuniformity.

`canonical_selection_written` proves the *same* `PrescribedSelection.CanonicalSelection d` as the
repository's `canonical_selection` (which obtains the rearranged minimizer from the closure of the
finite polarization orbit, `SuccessiveCoordinateRearrangement`/`PrescribedSteinerSelection`), but
with this composition.  The a.e. chain `AESuccessiveSteiner ρ η` is obtained from the measurable chain
`MeasSuccessive` (`MeasSuccessive.toSteiner`, `MeasChain.congr_left`) of `coordinate_rearranged_minimizer`
applied to the continuous Gibbs representative of `ρ`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.HighDim BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open CoordinateRearrangementStatement BecknerOnofri.V2.Rearrangement

/-- The statement of `PrescribedSelection.canonical_selection`, proved by the written-route wrapper
`coordinate_rearranged_minimizer` and the cosine representation `cosine_representation`. -/
theorem canonical_selection_written {d : ℕ} (hd : 0 < d) : CanonicalSelection d := by
  intro β hβ _hβd ρ hρ
  obtain ⟨v, hv, hm0, hvs, _, hvmax, he⟩ := continuous_optimizer_of_minimizer hd hβ ρ hρ
  let ρ₀ := continuousGibbsDensity v
  have he₀ : ρ.value =ᵐ[torusMeasure d] ρ₀.value := he
  have hρ₀ : IsGlobalMinimizer β ρ₀ := (minimizer_congr_ae he₀ β).mp hρ
  have hρ₀s : SmoothOnTorus ρ₀.value := normalizedGibbs_smooth v hvs
  obtain ⟨η, u, hch, hηmin, -, -, hD, -, -, -, hgu, hηs, hηpos, hus, hm, hu, hG, heuler, hst,
    hstu⟩ := coordinate_rearranged_minimizer hd hβ ρ₀ hρ₀ hρ₀s
  obtain ⟨U, -, -, -, hM⟩ := GeneralEulerBridge.cosine_representation hd β hβ u η hus hm hstu hgu
    heuler
  have hD₀ : IdentDistrib η.value ρ.value (torusMeasure d) (torusMeasure d) :=
    hD.trans (IdentDistrib.of_ae_eq ρ₀.integrable.aemeasurable he₀.symm)
  refine ⟨η, u, MeasSuccessive.toSteiner (MeasChain.congr_left hch he₀), hηmin, hD₀,
    (hD₀.comp Real.continuous_mul_log.measurable).integral_eq,
    (minimizer_value_eq_pressure hηmin).trans (minimizer_value_eq_pressure hρ).symm,
    hgu, hηs, hηpos, hus, hu, fun s => SmoothTorus.smooth_mem_sobolev hus s, hm, hG, hst, hstu, hM,
    minimizer_green_fourier_nonnegative hd hβ η hηmin hM u hm hG, ?_⟩
  intro hnon hh
  exact hnon (hD₀.ae_snd (measurableSet_singleton 1) hh)

/-- **`lem:selection-full-entropy-domain`** (Lemma 2.13) in the repository's vocabulary, `d ≥ 1`
(the manuscript takes `d ≥ 2`; the argument has no use for it), `0 < β < 2d`:

* (i) a global minimizer of `ℰ_β` over finite-entropy densities exists, and every minimizer is a.e.
  a smooth strictly positive function equal a.e. to the Gibbs density of its Green potential, with the
  Euler relation in Fourier variables;
* (ii), (iii) `CanonicalSelection d`: for every minimizer there are a successive rearrangement `η`
  and potential `u` with `η` a minimizer of the same entropy, energy (`pressureValue`) and
  distribution, `η = normalizedGibbs u`, `η, u` smooth, `η > 0`, `u` mean zero, separately even and
  nonincreasing in each coordinate, `η` a countable cosine mixture, `η̂, û ≥ 0`, and `ρ ≢ 1 → η ≢ 1`.

Status: proved with the written-route wrapper (`canonical_selection_written`), see the module header. -/
theorem selection_full_entropy_domain_written {d : ℕ} (hd : 0 < d) :
    (∀ β : ℝ, 0 < β → β < 2 * (d : ℝ) → ∃ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ) ∧
    (∀ β : ℝ, 0 < β → ∀ ρ : ProbabilityDensity d, IsGlobalMinimizer β ρ →
      (∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
      ρ.value =ᵐ[torusMeasure d] normalizedGibbs (Gap.densityPotential β ρ.value) ∧
      (∀ k : NonzeroFrequency d,
        (frequencyLength k.val ^ d : ℂ) * fourierCoeff (Gap.densityPotential β ρ.value) k.val =
          (β / spectralThreshold d : ℝ) * fourierCoeff ρ.value k.val)) ∧
    CanonicalSelection d :=
  ⟨fun _ hβ hβd => exists_minimizer hd hβ hβd,
    fun _ hβ ρ hρ => minimizer_smooth_positive_kirkwood hd hβ ρ hρ,
    canonical_selection_written hd⟩

#print axioms canonical_selection_written
#print axioms selection_full_entropy_domain_written

end BecknerOnofri.V2.Reaudit.Mixtures
