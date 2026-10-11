module

public import BecknerOnofri.V2.Rearrangement.Comparison
public import BecknerOnofri.GeneralEuler.Paper
public import BecknerOnofri.CanonicalSelectionDefinitions
public import BecknerOnofri.CanonicalSelectionFourier
public import BecknerOnofri.SmoothTorusSobolev
public import BecknerOnofri.V2.Reaudit.Attainment.Main
public import BecknerOnofri.V2.Reaudit.Attainment.Regularity
public import BecknerOnofri.V2.Reaudit.Attainment.PotentialFourier

@[expose] public section

/-! # Lemma 2.13 `lem:selection-full-entropy-domain` through the written-route wrapper (S016)

The printed proof of the entropy-preserving selection is

* (i) attainment and smoothness/positivity of minimizers: Proposition
  `prop:section2-subcritical-attainment` and Corollary `cor:section2-extremizer-correspondence` (iii),
  i.e. the `Reaudit.Attainment` package (`subcritical_attainment`, `densityMinimizer_regularity`,
  `fourierCoeff_densityPotential`; rows S009, S010);
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
with this composition; the smooth positive starting minimizer is the representative of the given
minimizer supplied by `Reaudit.Attainment.subcritical_attainment` (`exists_smooth_positive_representative`),
and no declaration of `OptimizerDuality` is used.  The a.e. chain `AESuccessiveSteiner ρ η` is obtained from the measurable chain
`MeasSuccessive` (`MeasSuccessive.toSteiner`, `MeasChain.congr_left`) of `coordinate_rearranged_minimizer`
applied to the continuous Gibbs representative of `ρ`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.HighDim BecknerOnofri.HighDim.PrescribedSelection
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers OptimizerDuality
open CoordinateRearrangementStatement BecknerOnofri.V2.Rearrangement

/-- **Smooth initial minimizer** (`prop:section2-subcritical-attainment`, third assertion): a
minimizer `ρ` at `0 < β < 2d` is a.e. equal to a smooth strictly positive probability density
`ρ₀`, which is again a minimizer.  The regularity is that of the `Attainment` package. -/
theorem exists_smooth_positive_representative {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (hβd : β < 2 * (d : ℝ)) (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    ∃ ρ₀ : ProbabilityDensity d, ρ.value =ᵐ[torusMeasure d] ρ₀.value ∧ IsGlobalMinimizer β ρ₀ ∧
      SmoothOnTorus ρ₀.value ∧ ∀ x, 0 < ρ₀.value x := by
  obtain ⟨-, -, hreg, -⟩ := Reaudit.Attainment.subcritical_attainment hd hβ hβd
  obtain ⟨q, hq, hqs, hqp⟩ := hreg ρ hρ
  let ρ₀ : ProbabilityDensity d :=
    { value := q
      nonneg := Filter.Eventually.of_forall fun x => (hqp x).le
      integrable := ρ.integrable.congr hq
      mass := by rw [← integral_congr_ae hq]; exact ρ.mass }
  exact ⟨ρ₀, hq, (minimizer_congr_ae hq β).1 hρ, hqs, hqp⟩

/-- **Regularity of every attained minimizer** (`cor:section2-extremizer-correspondence` (iii)), for
every `β > 0` (including the attained endpoint): a minimizer is a.e. smooth and strictly positive,
equals a.e. the Gibbs density of its Green potential, and satisfies the Euler relation in Fourier
variables.  Same statement as the second conjunct of `selection_full_entropy_domain_written` (the
former `OptimizerDuality.minimizer_smooth_positive_kirkwood`), proved from the `Attainment` package. -/
theorem minimizer_regular_gibbs_euler {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) :
    (∃ q : Torus d → ℝ, ρ.value =ᵐ[torusMeasure d] q ∧ SmoothOnTorus q ∧ ∀ x, 0 < q x) ∧
      ρ.value =ᵐ[torusMeasure d] normalizedGibbs (Gap.densityPotential β ρ.value) ∧
      (∀ k : NonzeroFrequency d,
        (frequencyLength k.val ^ d : ℂ) * fourierCoeff (Gap.densityPotential β ρ.value) k.val =
          (β / spectralThreshold d : ℝ) * fourierCoeff ρ.value k.val) := by
  have hA0 : 0 < Gap.coefficient d β := Gap.coefficient_pos hd hβ
  have hback := Reaudit.Attainment.coefficient_coefficient hd hβ
  refine ⟨(Reaudit.Attainment.attained_extremizers_regular hd hβ (Or.inr ⟨ρ, hρ⟩)).2.2.1 ρ hρ,
    ?_, fun k => ?_⟩
  · obtain ⟨v, hvu, -, -, -, -, hρv⟩ := Reaudit.Attainment.densityMinimizer_regularity hd hA0 ρ
      (by rw [hback]; exact hρ)
    rw [hback] at hvu
    exact hρv.trans (Gap.gibbs_congr hvu)
  · simpa only [Complex.ofReal_pow] using
      Reaudit.Attainment.fourierCoeff_densityPotential hd hβ ρ hρ.1 k.property

/-- Nonnegativity of the Fourier coefficients of a minimizing cosine mixture and of its Green
potential: the statement of `PrescribedSelection.minimizer_green_fourier_nonnegative`, with the
Euler relation in Fourier variables taken from `minimizer_regular_gibbs_euler` (the `Attainment`
package) instead of `OptimizerDuality.minimizer_smooth_positive_kirkwood`. -/
theorem minimizer_green_fourier_nonnegative_aligned {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (ρ : ProbabilityDensity d) (hρ : IsGlobalMinimizer β ρ) (hM : IsCountableCosineMixture ρ)
    (u : Torus d → ℝ) (hm : MeanZero u)
    (hG : u =ᵐ[torusMeasure d] Gap.densityPotential β ρ.value) :
    ∀ k : Frequency d, 0 ≤ (fourierCoeff ρ.value k).re ∧ (fourierCoeff ρ.value k).im = 0 ∧
      0 ≤ (fourierCoeff u k).re ∧ (fourierCoeff u k).im = 0 := by
  intro k
  obtain ⟨hR, hI⟩ := mixture_fourier_nonnegative ρ hM k
  refine ⟨hR, hI, ?_⟩
  by_cases hk : k = 0
  · subst k
    have hz : fourierCoeff u 0 = 0 := by
      simp only [BecknerOnofri.HighDim.fourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
        ContinuousMap.one_apply,
        one_mul]
      rw [integral_complex_ofReal, show (∫ x, u x ∂torusMeasure d) = 0 from hm]
      rfl
    simp [hz]
  · have he := (minimizer_regular_gibbs_euler hd hβ ρ hρ).2.2 ⟨k, hk⟩
    rw [← fourierCoeff_congr_ae hG] at he
    have hp : 0 < frequencyLength k ^ d := lt_of_lt_of_le zero_lt_one
      (GreenCritical.nonzero_eigenvalue_ge_one ⟨k, hk⟩)
    have hβσ : 0 ≤ β / spectralThreshold d := (div_pos hβ (spectralThreshold_pos hd)).le
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, hI] at hr hi
    constructor
    · nlinarith [mul_nonneg hβσ hR]
    · nlinarith

/-- The statement of `PrescribedSelection.canonical_selection`, proved by the written-route wrapper
`coordinate_rearranged_minimizer` and the cosine representation `cosine_representation`. -/
theorem canonical_selection_written {d : ℕ} (hd : 0 < d) : CanonicalSelection d := by
  intro β hβ hβd ρ hρ
  obtain ⟨ρ₀, he₀, hρ₀, hρ₀s, -⟩ := exists_smooth_positive_representative hd hβ hβd ρ hρ
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
    minimizer_green_fourier_nonnegative_aligned hd hβ η hηmin hM u hm hG, ?_⟩
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
  ⟨fun _ hβ hβd => (Reaudit.Attainment.subcritical_attainment hd hβ hβd).2.1,
    fun _ hβ ρ hρ => minimizer_regular_gibbs_euler hd hβ ρ hρ,
    canonical_selection_written hd⟩

#print axioms exists_smooth_positive_representative
#print axioms minimizer_regular_gibbs_euler
#print axioms minimizer_green_fourier_nonnegative_aligned
#print axioms canonical_selection_written
#print axioms selection_full_entropy_domain_written

end BecknerOnofri.V2.Reaudit.Mixtures
