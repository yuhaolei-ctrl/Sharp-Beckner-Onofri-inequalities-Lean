module

public import BecknerOnofri.EndpointRigidity.RawDensity
public import BecknerOnofri.MixtureMarginalEnergyPaper
public import BecknerOnofri.EntropyShearer.PaperStatement
public import BecknerOnofri.V2.Reaudit.Mixtures.DirectTransfer

@[expose] public section

/-! # Lemma 5.2, Proposition 5.5 and Proposition 5.7 (`lem:spectral-subset-entropy`,
`prop:spectral-marginal-energy`, `prop:spectral-dimension-transfer`)

All declarations are thin wrappers (in `BecknerOnofri.V2.Transfer`) around repository declarations
whose constant-level dependency closure contains none of the old endpoint modules; see
`RESOLUTION.md`.

Dictionary.  The repository writes the energy `(2π)^d ‖ρ‖²_{Ḣ^{-d/2}(𝕋^d)}` as
`spectralEnergy ρ = ∑_{k≠0} |k|^{-d} |ρ̂(k)|²` (an `ℝ≥0∞`-valued sum), and the energy
`(2π)^r ‖ρ_I‖²_{Ḣ^{-r/2}(𝕋^r)}` of a coordinate marginal as `inversePowerEnergy r (coordinateMarginal ρ I)`
where the marginal is a function on the ambient torus that does not depend on the coordinates
outside `I` (so that its only nonzero Fourier coefficients are supported on `I`).  Marginal entropies
are `coordinateMarginalEntropy ρ I = ∫ ρ_I log ρ_I dm_d`, which equals the entropy on `𝕋^I` because
`m_d` has mass one. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BecknerOnofri.V2.Transfer
open BecknerOnofri.HighDim

/-! ## Lemma 5.2: Shearer's inequality for all `r`-subsets -/

/-- **Lemma 5.2.**  For every finite-entropy probability density `ρ` on `𝕋^d` and `1 ≤ r ≤ d`
all marginals have finite entropy and `Ent(ρ) ≥ d / (r C(d,r)) ∑_{|I|=r} Ent(ρ_I)`. -/
theorem spectral_subset_entropy {d r : ℕ} (hr : 1 ≤ r) (hrd : r ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    (∀ I : Finset (Fin d),
      Integrable (fun x => coordinateMarginal ρ I x * Real.log (coordinateMarginal ρ I x))
        (torusMeasure d)) ∧
    (d : ℝ) / ((r : ℝ) * (d.choose r : ℝ)) *
        (∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r, coordinateMarginalEntropy ρ I)
      ≤ entropy ρ :=
  ⟨fun I => (EntropyShearer.coordinateMarginal_finiteEntropy ρ hρ I).1,
    EntropyShearer.subset_entropy hr hrd ρ hρ⟩

/-! ## Proposition 5.5: energy comparison for cosine-power mixtures -/

/-- **Proposition 5.5**, first display (deletion of one coordinate).  `hρ : IsCountableCosineMixture ρ`
is the representation (eq:mixture) with an arbitrary (correlated) countable weight family. -/
theorem spectral_marginal_energy_deletion {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : IsCountableCosineMixture ρ) :
    spectralEnergy ρ ≤ ENNReal.ofReal (1 / ((d : ℝ) - 1)) *
      ∑ i : Fin d, inversePowerEnergy (d - 1) (coordinateMarginal ρ (Finset.univ.erase i)) :=
  BecknerOnofri.V2.Reaudit.Mixtures.spectral_marginal_energy_deletion_direct hd ρ hρ

/-- **Proposition 5.5**, second display (all `r`-subsets, `d ≥ r ≥ 12`). -/
theorem spectral_marginal_energy_subset {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (ρ : ProbabilityDensity d) (hρ : IsCountableCosineMixture ρ) :
    spectralEnergy ρ ≤ ENNReal.ofReal ((d : ℝ) / ((r : ℝ) * (d.choose r : ℝ))) *
      ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        inversePowerEnergy r (coordinateMarginal ρ I) :=
  BecknerOnofri.V2.Reaudit.Mixtures.spectral_marginal_energy_subset_direct hr hrd ρ hρ

/-- The vanishing step of the equality case of Proposition 5.7 (`eq:spectral-equality-conclusion`):
if every `r`-marginal of a cosine-power mixture has vanishing (nonnegative) Fourier contributions,
then so does the mixture itself, i.e. `0 ≤ (2π)^d ‖ρ‖² ≤ ∑ (2π)^r ‖0‖² = 0`; consequently all its nonzero
Fourier coefficients vanish. -/
theorem mixture_energy_vanishes_of_marginals {d r : ℕ} (hr : 12 ≤ r) (hrd : r ≤ d)
    (ρ : ProbabilityDensity d) (hρ : IsCountableCosineMixture ρ)
    (hI : ∀ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
      inversePowerEnergy r (coordinateMarginal ρ I) = 0) :
    spectralEnergy ρ = 0 ∧ ∀ k : Frequency d, k ≠ 0 → fourierCoeff ρ.value k = 0 := by
  have h := spectral_marginal_energy_subset hr hrd ρ hρ
  rw [Finset.sum_eq_zero hI, mul_zero] at h
  have h0 : spectralEnergy ρ = 0 := le_antisymm h (zero_le)
  refine ⟨h0, fun k hk => ?_⟩
  unfold spectralEnergy at h0
  have := (ENNReal.tsum_eq_zero.mp h0) ⟨k, hk⟩
  rw [ENNReal.ofReal_eq_zero] at this
  have hlen : 0 < frequencyLength k := by
    unfold frequencyLength
    apply Real.sqrt_pos.mpr
    by_contra hneg
    apply hk
    funext i
    have hs : ∑ i : Fin d, ((k i : ℤ) : ℝ) ^ 2 = 0 :=
      le_antisymm (not_lt.mp hneg) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((k i : ℤ) : ℝ))).mp hs i
      (Finset.mem_univ i)
    simpa using this
  have hp : 0 < (frequencyLength k ^ d)⁻¹ := by positivity
  have hsq : ‖fourierCoeff ρ.value k‖ ^ 2 = 0 := by
    change (frequencyLength k ^ d)⁻¹ * ‖fourierCoeff ρ.value k‖ ^ 2 ≤ 0 at this
    nlinarith [sq_nonneg ‖fourierCoeff ρ.value k‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp hsq)

/-! ## Proposition 5.7: transfer from dimension twelve (conditional) -/

/-- The inequality of Proposition `prop:spectral-d12-base` (dimension twelve): for every finite-entropy
probability density `ρ` on `𝕋^12`, `Ent(ρ) ≥ (2π)^12/2 ‖ρ‖²_{Ḣ^{-6}}`, i.e. with
`spectralEnergy ρ = (2π)^12 ‖ρ‖²_{Ḣ^{-6}}`, `½ spectralEnergy ρ ≤ Ent ρ`.  (Stated as
`spectralEnergy ρ ≤ ofReal (2 Ent ρ)`; see `spectralD12Inequality_iff`.)  This is a hypothesis of the
conditional theorems below, not a consequence of them. -/
def SpectralD12Inequality : Prop :=
  ∀ ρ : ProbabilityDensity 12, ρ.FiniteEntropy →
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ)

/-- The equality case in dimension twelve: equality in the inequality holds only for the uniform
density, `ρ = 1` `m_12`-a.e. -/
def SpectralD12Equality : Prop :=
  ∀ ρ : ProbabilityDensity 12, ρ.FiniteEntropy →
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) →
      ρ.value =ᵐ[torusMeasure 12] fun _ => 1

theorem spectralD12Inequality_iff : SpectralD12Inequality ↔
    ∀ ρ : ProbabilityDensity 12, ρ.FiniteEntropy →
      (1 / 2 : ℝ≥0∞) * spectralEnergy ρ ≤ ENNReal.ofReal (entropy ρ) := by
  have key : ∀ (a : ℝ≥0∞) (e : ℝ), 0 ≤ e →
      (a ≤ ENNReal.ofReal (2 * e) ↔ (1 / 2 : ℝ≥0∞) * a ≤ ENNReal.ofReal e) := by
    intro a e he
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    constructor
    · intro h
      calc (1 / 2 : ℝ≥0∞) * a ≤ (1 / 2 : ℝ≥0∞) * (2 * ENNReal.ofReal e) :=
            mul_le_mul_right h _
        _ = ENNReal.ofReal e := by
            rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    · intro h
      calc a = 2 * ((1 / 2 : ℝ≥0∞) * a) := by
            rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * ENNReal.ofReal e := mul_le_mul_right h _
  constructor
  · intro h ρ hρ
    exact (key _ _ (entropy_nonneg ρ hρ)).mp (h ρ hρ)
  · intro h ρ hρ
    exact (key _ _ (entropy_nonneg ρ hρ)).mpr (h ρ hρ)

/-- **Proposition 5.7, inequality.**  Assume the dimension-twelve inequality.  Then for every integer
`d ≥ 12` and every finite-entropy probability density `ρ` on `𝕋^d`,
`Ent(ρ) ≥ (2π)^d/2 ‖ρ‖²_{Ḣ^{-d/2}}`. -/
theorem spectral_dimension_transfer_inequality (h12 : SpectralD12Inequality) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) :=
  CosineMixtureTransfer.density_endpoint_of_twelve_density h12 hd ρ hρ

/-- The dimension-twelve inequality gives the legacy cosine-mixture base, and the dimension-twelve
equality case gives the legacy mixture rigidity. -/
theorem mixtureRigidity_twelve (h12 : SpectralD12Inequality) (hEq : SpectralD12Equality) :
    EndpointRigidity.MixtureRigidity 12 := by
  have hE : CosineMixtureTransfer.MixtureEndpoint 12 :=
    CosineMixtureTransfer.mixture_endpoint_of_density (by norm_num) h12
  refine EndpointRigidity.mixtureRigidity_of_densityRigidity (by norm_num) ?_
  intro r hr he
  have hfe := CosineMixtureTransfer.finite_entropy_endpoint_from_mixture (by norm_num) hE r hr
  have hraw : (Bridge.rawDensity r).FiniteEntropy := hr
  have hsp : spectralEnergy (Bridge.rawDensity r) = ENNReal.ofReal (2 * entropy (Bridge.rawDensity r)) := by
    rw [Bridge.rawDensity_spectralEnergy r hfe.1]
    congr 1
    change Legacy.BecknerOnofri.fourierEnergy r = 2 * Legacy.TorusEndpoint.densityEntropy r.value
    linarith
  exact hEq (Bridge.rawDensity r) hraw hsp

/-- **Proposition 5.7, equality case.**  Assume the dimension-twelve inequality and that equality in
dimension twelve holds only for the uniform density.  Then for every integer `d ≥ 12` and every
finite-entropy probability density `ρ` on `𝕋^d`, equality in the transferred inequality holds if and
only if `ρ = 1` almost everywhere. -/
theorem spectral_dimension_transfer_equality (h12 : SpectralD12Inequality)
    (hEq : SpectralD12Equality) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔ ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
  density_rigidity_from_twelve (CosineMixtureTransfer.mixture_endpoint_of_density (by norm_num) h12)
    (mixtureRigidity_twelve h12 hEq) hd ρ hρ

/-- **Proposition 5.7** (conditional on the explicit dimension-twelve inequality and equality case). -/
theorem spectral_dimension_transfer (h12 : SpectralD12Inequality) (hEq : SpectralD12Equality)
    {d : ℕ} (hd : 12 ≤ d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1) :=
  ⟨spectral_dimension_transfer_inequality h12 hd ρ hρ,
    spectral_dimension_transfer_equality h12 hEq hd ρ hρ⟩

end BecknerOnofri.V2.Transfer
