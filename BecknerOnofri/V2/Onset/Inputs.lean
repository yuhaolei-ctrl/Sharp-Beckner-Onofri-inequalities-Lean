module

public import BecknerOnofri.ExtendedEntropy
public import BecknerOnofri.EndpointDuality
public import BecknerOnofri.OnsetCompactness

@[expose] public section

/-! # Interface hypotheses for the global onset theorem (Proposition 5.24)

The proof of Proposition 5.24 (manuscript `subsec:section5-lyapunov-schmidt`) uses exactly two
facts from Corollary 5.8 (`cor:section5-high-endpoint`), valid for `d ≥ 12`:

* the spectral inequality `eq:spectral-density-conclusion`:
  `Ent(ρ) ≥ (2π)^d/2 ‖ρ‖²_{Ḣ^{-d/2}}`, i.e. in the vocabulary of `Challenge.lean`
  `spectralEnergy ρ ≤ 2 Ent(ρ)` for every finite-entropy density; it gives `P_d(β_s(d)) = 0`
  (`eq:section5-endpoint-unique-minimizer`) and `Φ_{d,1} ≤ 0` (so a limit of the dual maximizers is
  a spectral optimizer);
* the forward direction of the equality case: equality `spectralEnergy ρ = 2 Ent(ρ)` forces
  `ρ ≡ 1` a.e.; this is the step "the equality case in Corollary 5.8 implies `u_* = 0`"
  (`eq:section5-onset-limit-maximizer`).

They are NOT proved in this package.  They are the manuscript's intermediate statements (for
a fixed dimension `d`, to be instantiated at `d ≥ 12`), not the onset conclusion, and they are
carried as explicit named hypotheses of every conditional onset theorem.  The two bridges below
show that they follow literally from the displayed statements of Theorem 1.3 as formalized in
`Challenge.lean` (`high_dim_entropy_inequality`, `high_dim_entropy_eq_iff`). -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim

/-- **Cor. 5.8, inequality (`eq:spectral-density-conclusion`).**  For every finite-entropy
probability density, `spectralEnergy ρ ≤ 2 Ent(ρ)`. -/
def SpectralEndpointInequality (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy → spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ)

/-- **Cor. 5.8, forward direction of the equality case.**  A finite-entropy density with
`spectralEnergy ρ = 2 Ent(ρ)` is a.e. equal to the uniform density. -/
def DensityRigidityForward (d : ℕ) : Prop :=
  ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) → ρ.value =ᵐ[torusMeasure d] fun _ => 1

/-- `Challenge.high_dim_entropy_inequality` (at a given `d`) implies the spectral inequality. -/
theorem SpectralEndpointInequality.of_extended (d : ℕ)
    (h : ∀ ρ : ProbabilityDensity d,
      ((1 / 2 : ℝ) : EReal) * (spectralEnergy ρ).toEReal ≤ extendedEntropy ρ) :
    SpectralEndpointInequality d := by
  intro ρ hρ
  have h := h ρ
  rw [extendedEntropy_eq ρ hρ] at h
  by_cases hE : spectralEnergy ρ = ⊤
  · rw [hE] at h
    simp at h
    rw [EReal.coe_mul_top_of_pos (by norm_num : (0:ℝ) < 2⁻¹)] at h
    exact absurd (top_le_iff.mp h) (EReal.coe_ne_top _)
  · rw [← EReal.coe_ennreal_toReal hE] at h
    have h2 : (1 / 2 : ℝ) * (spectralEnergy ρ).toReal ≤ entropy ρ := by exact_mod_cast h
    rw [← ENNReal.ofReal_toReal hE]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- `Challenge.high_dim_entropy_eq_iff` (at a given `d`) implies the forward direction. -/
theorem DensityRigidityForward.of_iff (d : ℕ)
    (h : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1)) :
    DensityRigidityForward d := fun ρ hρ => (h ρ hρ).mp

/-! ## Bridges to the legacy vocabulary of the existing onset infrastructure

The existing conditional onset lemmas (`OnsetCompactness`, `GlobalPressureOnset`,
`OnsetContinuous`, `OrderParameterOnset`, ...) take the hypotheses
`EndpointRigidity.CoefficientEndpoint d (1/2)` and `OnsetCompactness.DensityRigidity d`, stated for
`Legacy.TorusEndpoint.ProbabilityDensity` with real-valued `fourierEnergy`.  The following bridge
lemmas show that they are consequences of `SpectralEndpointInequality d` and
`DensityRigidityForward d` (no further input). -/

theorem SpectralEndpointInequality.summable_and_energy {d : ℕ} (hE : SpectralEndpointInequality d)
    (r : Legacy.TorusEndpoint.ProbabilityDensity d) (hr : r.FiniteEntropy) :
    Summable (Legacy.TorusEndpoint.densitySpectralTerm r) ∧
      spectralEnergy (Bridge.rawDensity r) = ENNReal.ofReal (Legacy.BecknerOnofri.fourierEnergy r) := by
  have hρ : (Bridge.rawDensity r).FiniteEntropy := hr
  have h := hE (Bridge.rawDensity r) hρ
  have hlt : spectralEnergy (Bridge.rawDensity r) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have he : spectralTerm (Bridge.rawDensity r) = Legacy.TorusEndpoint.densitySpectralTerm r := by
    funext k
    exact (Bridge.densitySpectralTerm_eq (Bridge.rawDensity r) k).symm
  have hn (k : NonzeroFrequency d) : 0 ≤ Legacy.TorusEndpoint.densitySpectralTerm r k := by
    unfold Legacy.TorusEndpoint.densitySpectralTerm
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
  have hs : Summable (Legacy.TorusEndpoint.densitySpectralTerm r) := by
    have := ENNReal.summable_toReal (f := fun k => ENNReal.ofReal (spectralTerm (Bridge.rawDensity r) k))
      hlt
    refine this.congr fun k => ?_
    rw [he, ENNReal.toReal_ofReal (hn k)]
  exact ⟨hs, Bridge.rawDensity_spectralEnergy r hs⟩

/-- `SpectralEndpointInequality d` gives the legacy `CoefficientEndpoint d (1/2)`. -/
theorem SpectralEndpointInequality.toCoefficientEndpoint {d : ℕ} (hE : SpectralEndpointInequality d) :
    EndpointRigidity.CoefficientEndpoint d (1 / 2) := by
  intro r hr
  obtain ⟨hs, hen⟩ := hE.summable_and_energy r hr
  refine ⟨hs, ?_⟩
  have hρ : (Bridge.rawDensity r).FiniteEntropy := hr
  have h := hE (Bridge.rawDensity r) hρ
  rw [hen] at h
  have hn : 0 ≤ 2 * entropy (Bridge.rawDensity r) :=
    mul_nonneg (by norm_num) (entropy_nonneg _ hρ)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hn).mp h
  change Legacy.BecknerOnofri.fourierEnergy r ≤ 2 * Legacy.TorusEndpoint.densityEntropy r.value at hreal
  linarith

/-- The two inputs give the legacy `DensityRigidity d`. -/
theorem DensityRigidityForward.toDensityRigidity {d : ℕ} (hE : SpectralEndpointInequality d)
    (hR : DensityRigidityForward d) : OnsetCompactness.DensityRigidity d := by
  intro r hr heq
  obtain ⟨_, hen⟩ := hE.summable_and_energy r hr
  have hρ : (Bridge.rawDensity r).FiniteEntropy := hr
  have h2 : spectralEnergy (Bridge.rawDensity r) = ENNReal.ofReal (2 * entropy (Bridge.rawDensity r)) := by
    rw [hen]
    congr 1
    change Legacy.BecknerOnofri.fourierEnergy r = 2 * Legacy.TorusEndpoint.densityEntropy r.value
    linarith
  exact hR (Bridge.rawDensity r) hρ h2

/-- The two inputs of the global onset argument, for one dimension. -/
structure OnsetEndpointInputs (d : ℕ) : Prop where
  inequality : SpectralEndpointInequality d
  rigidity : DensityRigidityForward d

end BecknerOnofri.V2.Onset
