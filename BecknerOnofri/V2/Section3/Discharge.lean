module

public import BecknerOnofri.V2.Section3.Lemma31
public import BecknerOnofri.V2.Section3.LegacyBridge
public import BecknerOnofri.ContinuousMixtureMajorant
public import BecknerOnofri.MixtureEnergyStatementBridge
public import Legacy.BecknerOnofri.LowDimensionMixtureEndpoint
public import Legacy.BecknerOnofri.StrictCountableMixture

@[expose] public section

/-! # Discharge of the two hypotheses of Lemma 3.1 on smooth strictly positive mixtures (G04)

`mixtureInequality_smooth` / `mixtureStrictness_smooth` (`2 ≤ d ≤ 10`) prove the two conditional
inputs of Lemma 3.1 for every smooth strictly positive finite-entropy countable cosine-power mixture
(which is all the proof of Lemma 3.1 uses, see `Lemma31.lean`).  They are obtained from the repository
mixture/scalar route: the finite scalar inequality of Proposition 3.4 (`LowScalar.scalar_gap`'s
legacy form `Legacy.D10.FiniteScalar` / `Gaussian` bounds), the hypergeometric identity of Lemma 3.3,
the circle marginal entropy bound of Lemma 3.2, assembled in
`Legacy.BecknerOnofri.LowDimensionMixtureEndpoint.countable_mixture_endpoint` and
`Legacy.BecknerOnofri.StrictMixture.countable_mixture_gap`.  The majorant hypothesis `hSup`
(summable `w n * h_{N n}(0)`) of those theorems is derived from the continuity of the density
(`CosineMixtureTransfer.mixture_majorant_of_continuous`); it is not assumed.

The class of *all* finite-entropy mixtures (including unbounded ones) is **not** treated here; see
`RESOLUTION.md` (remaining obligation R1). -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim BecknerOnofri.V2.Vocab

variable {d : ℕ}

/-- The data of a smooth countable cosine-power mixture, with the majorant derived. -/
theorem smoothMixture_data {ρ : ProbabilityDensity d} (hs : SmoothOnTorus ρ.value)
    (hmix : IsCountableCosineMixture ρ) :
    ∃ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (_ : ∀ n, 0 ≤ w n) (_ : HasSum w 1)
      (_ : Summable fun n => w n * Legacy.BecknerOnofri.CosineMixture.tensor (N n) 0),
      ρ.value =ᵐ[torusMeasure d]
        Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := by
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  obtain ⟨K, hK⟩ := hs.exists_lipschitz
  have he' : ρ.value =ᵐ[torusMeasure d]
      Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  exact ⟨w, N, hw, hm, CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value
    hK.continuous w N hw hm.summable he', he'⟩

/-- **The mixture inequality on smooth strictly positive mixtures**, `2 ≤ d ≤ 10`. -/
theorem mixtureInequality_smooth (hd2 : 2 ≤ d) (hd10 : d ≤ 10) : SmoothMixtureInequality d := by
  intro ρ hρ hsm
  obtain ⟨w, N, hw, hm, hSup, he⟩ := smoothMixture_data hsm.1 hsm.2.2
  have h := Legacy.BecknerOnofri.LowDimensionMixtureEndpoint.countable_mixture_endpoint hd2 hd10
    w N hw hm hSup
  have := entropyBound_add_of_legacy (g := 0) (by omega) ρ hρ
    (Legacy.BecknerOnofri.CosineMixtureApproximation.probabilityDensity w N hw hm hSup) he
    h.1 (by simpa using h.2)
  unfold EntropyBound
  linarith

/-- **The mixture strictness on smooth strictly positive mixtures**, `2 ≤ d ≤ 10`. -/
theorem mixtureStrictness_smooth (hd2 : 2 ≤ d) (hd10 : d ≤ 10) : SmoothMixtureStrictness d := by
  intro ρ hρ hsm hnon
  obtain ⟨w, N, hw, hm, hSup, he⟩ := smoothMixture_data hsm.1 hsm.2.2
  -- a nonuniform mixture has a component with positive weight and a nonzero index
  have hcomp : ∃ a, 0 < w a ∧ N a ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hnon
    have hall : ∀ n, 0 < w n → N n = 0 := fun n hn => by
      by_contra hne; exact absurd (hno n hn) (by simpa using hne)
    have h1 := Legacy.BecknerOnofri.StrictMixture.countable_uniform_of_no_component
      w N hw hm hall
    filter_upwards [he] with x hx
    rw [hx]
    exact h1 x
  obtain ⟨a, ha, hNa⟩ := hcomp
  have hgap := Legacy.BecknerOnofri.StrictMixture.countable_mixture_gap hd2 hd10 w N hw hm hSup a hNa
  have hpositive : 0 < w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) *
      Legacy.BecknerOnofri.StrictMixture.gap d / 2 :=
    div_pos (mul_pos (mul_pos (mul_pos ha ha) (Legacy.BecknerOnofri.StrictMixture.latentWeight_self_pos (N a)))
      (Legacy.BecknerOnofri.StrictMixture.gap_pos (by omega))) (by norm_num)
  have hsumm : Summable (Legacy.TorusEndpoint.densitySpectralTerm
      (Legacy.BecknerOnofri.CosineMixtureApproximation.probabilityDensity w N hw hm hSup)) :=
    (Legacy.BecknerOnofri.LowDimensionMixtureEndpoint.countable_mixture_endpoint hd2 hd10
      w N hw hm hSup).1
  have := entropyBound_add_of_legacy (by omega) ρ hρ
    (Legacy.BecknerOnofri.CosineMixtureApproximation.probabilityDensity w N hw hm hSup) he hsumm
    hgap
  unfold EntropyStrict
  linarith

#print axioms mixtureInequality_smooth
#print axioms mixtureStrictness_smooth

end BecknerOnofri.V2.Section3
