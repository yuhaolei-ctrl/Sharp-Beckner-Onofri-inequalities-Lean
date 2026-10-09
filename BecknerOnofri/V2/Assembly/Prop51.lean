module

public import BecknerOnofri.V2.Assembly.GlobalGap
public import BecknerOnofri.V2.Transfer.All
public import BecknerOnofri.CanonicalSelectionFullDomain
public import BecknerOnofri.GeneralEuler.Paper
public import BecknerOnofri.OptimizerDuality
public import BecknerOnofri.OptimizerEulerPaper
public import BecknerOnofri.FiniteEntropyEnergy
public import BecknerOnofri.Uniform
public import BecknerOnofri.SmoothTorusDifferentiation
public import BecknerOnofri.SubcriticalGap
public import BecknerOnofri.V2.Vocab.HomEntropyTorus
public import BecknerOnofri.EndpointPackage

@[expose] public section

/-!
# Proposition 5.1 (`prop:spectral-d12-base`), work package G14

The dimension-twelve inequality `Ent(ρ) ≥ (2π)^12/2 ‖ρ‖²_{Ḣ^{-6}}` for every finite-entropy density on
`𝕋^12`, with equality only for `ρ = 1`.

Written proof (followed): the functional `Ent - ½ (2π)^12‖ρ‖²` attains its minimum (Lemma 2.13,
`OptimizerDuality.exists_minimizer`); the minimum is at most zero by the uniform competitor; from any
minimizer Lemma 2.13 supplies a smooth positive selected minimizer `ρ_u` with the same entropy
(`PrescribedSelection.canonical_selection`); Proposition 2.12 gives the global shape and the mixture
(`GeneralEulerBridge.cosine_representation`); `u` maximizes `Φ`, so Lemma 5.9 gives permutation
invariance (`Transfer.common_cubic_symmetry`); Proposition 5.10 (`global_entropy_gap`) gives
`0 ≥ Ent(ρ_u) - ½E(ρ_u) = -Φ(u) ≥ ρ̂_u(e_1)⁴/250 ≥ 0`; thus `ρ_u = 1`; entropy preservation makes the
original minimizer uniform; the minimum is zero and every equality density is a minimizer.

The only unproved input is `ScalarBounds` (Lemma 5.21, G13).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators ContDiff ENNReal
namespace BecknerOnofri.V2.Assembly
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.V2.Channel
open BecknerOnofri.V2.Transfer (IsPhiMaximizer Phi_eq_dualFunctional common_cubic_symmetry
  SpectralD12Inequality SpectralD12Equality)

/-! ### Bookkeeping: the two cosine cubes and the cosine partials -/

theorem cosineCube_eq (d : ℕ) :
    SmoothEulerStatement.cosineCube d = ConditionalEntropy.cosineCube d := rfl

theorem cosinePartial_sub_const {d : ℕ} (i : Fin d) (W : (Fin d → ℝ) → ℝ) (c : ℝ) :
    cosinePartial i (fun v => W v - c) = cosinePartial i W := by
  funext x
  unfold cosinePartial
  rw [fderivWithin_sub_const]

theorem cosinePartial_eq_coordinateDerivative {d : ℕ} (i : Fin d) (W : (Fin d → ℝ) → ℝ) :
    cosinePartial i W = SmoothEulerStatement.coordinateDerivative i W := rfl

/-! ### The pressure value at the spectral coupling -/

/-- For a finite-entropy density, `pressureValue β ρ = (β/(2β_s)) ∑_{k≠0} |k|^{-d}|ρ̂(k)|² - Ent ρ`
as an honest real number. -/
theorem pressureValue_eq_real {d : ℕ} (hd : 0 < d) (β : ℝ) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    pressureValue β ρ =
      ((β / (2 * spectralThreshold d) * (∑' k, spectralTerm ρ k) - entropy ρ : ℝ) : EReal) := by
  unfold pressureValue
  rw [spectralEnergy_coe_eq_tsum hd ρ hρ]
  push_cast
  rfl

theorem spectralEnergy_eq_ofReal {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) : spectralEnergy ρ = ENNReal.ofReal (∑' k, spectralTerm ρ k) :=
  (ENNReal.ofReal_tsum_of_nonneg
    (fun k => by unfold spectralTerm frequencyLength; positivity)
    (finiteEntropy_spectralTerm_summable hd ρ hρ)).symm

theorem spectralTerm_tsum_nonneg {d : ℕ} (ρ : ProbabilityDensity d) :
    0 ≤ ∑' k, spectralTerm ρ k :=
  tsum_nonneg (fun k => by unfold spectralTerm frequencyLength; positivity)

/-- At the spectral coupling the coefficient is `1/2`. -/
theorem pressureValue_spectral {d : ℕ} (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) :
    pressureValue (spectralThreshold d) ρ =
      (((1 / 2 : ℝ) * (∑' k, spectralTerm ρ k) - entropy ρ : ℝ) : EReal) := by
  rw [pressureValue_eq_real hd _ ρ hρ]
  have hσ := spectralThreshold_pos hd
  congr 3
  field_simp

theorem pressureValue_uniform_spectral : pressureValue (spectralThreshold 12) (uniformDensity 12) = 0 := by
  simp [pressureValue]

/-- A minimizer at the spectral coupling has `pressureValue ≥ 0` (uniform competitor). -/
theorem minimizer_half_energy_ge {ρ : ProbabilityDensity 12}
    (hρ : IsGlobalMinimizer (spectralThreshold 12) ρ) :
    entropy ρ ≤ (1 / 2 : ℝ) * (∑' k, spectralTerm ρ k) := by
  have h := hρ.2 (uniformDensity 12) (uniformDensity_finiteEntropy 12)
  rw [pressureValue_uniform_spectral, pressureValue_spectral (by norm_num) ρ hρ.1] at h
  have h' : (0 : ℝ) ≤ (1 / 2 : ℝ) * (∑' k, spectralTerm ρ k) - entropy ρ := by exact_mod_cast h
  linarith

/-! ### The uniform density is the only minimizer -/

/-- **Core of Proposition 5.1.**  Every global minimizer of `Ent - ½E` on `𝕋^12` is uniform.
This is the selection argument of the written proof (selected minimizer, global shape, symmetry, the
global entropy gap); it uses `ScalarBounds` only through Proposition 5.10. -/
theorem minimizer_uniform (hsc : ScalarBounds) (ρ : ProbabilityDensity 12)
    (hρ : IsGlobalMinimizer (spectralThreshold 12) ρ) :
    ρ.value =ᵐ[torusMeasure 12] fun _ => 1 := by
  have hd : 0 < 12 := by norm_num
  have hβ : 0 < spectralThreshold 12 := spectralThreshold_pos hd
  have hβd : spectralThreshold 12 < 2 * ((12 : ℕ) : ℝ) := by
    simpa using spectralThreshold_twelve_lt
  obtain ⟨η, u, -, hη, -, hent, hpv, hgu, hηs, hηp, hus, hu, -, hm, -, -, hstu, hmix, hnn, hnon⟩ :=
    PrescribedSelection.canonical_selection hd (spectralThreshold 12) hβ hβd ρ hρ
  -- `u` is a dual maximizer
  obtain ⟨u', -, hm', -, -, hmax', hg'⟩ :=
    OptimizerDuality.continuous_optimizer_of_minimizer hd hβ η hη
  have hcont : Continuous u := SmoothTorus.real_continuous hus
  let uS : ContinuousGibbs.Space 12 := ⟨u, hcont⟩
  have heq : uS = u' := OptimizerDuality.meanZero_gibbs_injective (u := uS) (v := u') hm hm' (by
    filter_upwards [hg'] with x hx
    rw [← hx, hgu]
    rfl)
  have hu_eq : u = (u' : Torus 12 → ℝ) := congrArg (fun f : ContinuousGibbs.Space 12 => (f : Torus 12 → ℝ)) heq
  have hmax : ∀ v : Torus 12 → ℝ, InCriticalSobolev v →
      dualFunctional (spectralThreshold 12) v ≤ dualFunctional (spectralThreshold 12) u := by
    rw [hu_eq]; exact hmax'
  have hPhi : IsPhiMaximizer 12 u := ⟨⟨hu, hm⟩, fun v hv => by
    rw [Phi_eq_dualFunctional hd, Phi_eq_dualFunctional hd]
    exact hmax v hv.1⟩
  -- permutation invariance (Lemma 5.9)
  have hN : ∀ k : Frequency 12, (fourierCoeff u k).im = 0 ∧ 0 ≤ (fourierCoeff u k).re :=
    fun k => ⟨(hnn k).2.2.2, (hnn k).2.2.1⟩
  have hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),
      η.value (fun i => x (π i)) = η.value x := by
    intro π x
    have h := common_cubic_symmetry hd hPhi hus hN π (fun _ => 1) (fun _ => Or.inl rfl) x
    simp only [one_smul] at h
    rw [hgu]
    simp only [normalizedGibbs, h]
  -- the Euler relation and Proposition 2.12
  have hE := OptimizerDuality.raw_optimizer_euler hd hβ u hu hm hmax
  obtain ⟨U, hU, hrep, hmp, -⟩ := GeneralEulerBridge.cosine_representation hd
    (spectralThreshold 12) hβ u η hus hm hstu hgu (by
      intro k
      have := hE k
      rw [← hgu] at this
      exact this)
  -- the potential `V = U - log Z`
  have hZ : 0 < ∫ y, Real.exp (u y) ∂torusMeasure 12 := by
    have h0 := hηp 0
    rw [hgu] at h0
    exact (div_pos_iff_of_pos_left (Real.exp_pos _)).mp h0
  set Z := ∫ y, Real.exp (u y) ∂torusMeasure 12 with hZdef
  let V : (Fin 12 → ℝ) → ℝ := fun v => U v - Real.log Z
  have hV : ContDiffOn ℝ ∞ V (cosineCube 12) := hU.sub contDiffOn_const
  have hlog : ∀ x, Real.log (η.value x) = V (cosineVector x) := by
    intro x
    obtain ⟨z, rfl⟩ := SmoothTorus.quotient_surjective 12 x
    have hc : cosineVector (SmoothTorus.quotient z) = fun j => Real.cos (2 * Real.pi * z j) := by
      funext j
      exact Legacy.BecknerOnofri.CosineMomentWeight.circleCos_coe (z j)
    rw [hc]
    show Real.log (η.value (fun i => (z i : UnitAddCircle))) = U _ - Real.log Z
    rw [hgu]
    simp only [normalizedGibbs]
    rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp, hrep z]
  have hP1 : ∀ i : Fin 12, cosinePartial i V = SmoothEulerStatement.coordinateDerivative i U :=
    fun i => cosinePartial_sub_const i U (Real.log Z)
  have h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v := by
    intro v hv i
    rw [hP1 i]
    exact hmp [i] (by simp) v hv
  have h2 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i (cosinePartial i V) v := by
    intro v hv i
    rw [hP1 i]
    exact hmp [i, i] (by simp) v hv
  obtain ⟨hgap, -, hrig⟩ := global_entropy_gap hsc η hηs hηp hperm hmix V hV hlog h1 h2
  -- the gap is nonpositive, so the first coefficient vanishes
  have hle := minimizer_half_energy_ge hη
  have hFE := EntropyTail.fullFourierEnergy_eq_spectral_tsum η
  have hnonpos : firstCoefficient η ^ 4 / 250 ≤ 0 := by
    refine hgap.trans ?_
    rw [hFE]
    linarith
  have hfc : firstCoefficient η = 0 := by
    have h4 : firstCoefficient η ^ 4 ≤ 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm h4 (by positivity))
  have hη1 : η.value = fun _ => 1 := hrig hfc
  by_contra hcon
  exact hnon hcon (by rw [hη1])

/-! ### Proposition 5.1: inequality and equality in dimension twelve -/

theorem spectral12_pos : 0 < spectralThreshold 12 := spectralThreshold_pos (by norm_num)

theorem spectral12_lt : spectralThreshold 12 < 2 * ((12 : ℕ) : ℝ) := by
  simpa using spectralThreshold_twelve_lt

/-- A minimizer exists (Lemma 2.13(i)); by `minimizer_uniform` it is uniform, and
`pressureValue` at it vanishes. -/
theorem exists_zero_minimizer (hsc : ScalarBounds) :
    ∃ ρ₀ : ProbabilityDensity 12, IsGlobalMinimizer (spectralThreshold 12) ρ₀ ∧
      pressureValue (spectralThreshold 12) ρ₀ = 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := OptimizerDuality.exists_minimizer (by norm_num : 0 < 12) spectral12_pos
    spectral12_lt
  have hu := minimizer_uniform hsc ρ₀ hρ₀
  have he : ρ₀.value =ᵐ[torusMeasure 12] (uniformDensity 12).value := hu
  exact ⟨ρ₀, hρ₀, by rw [OptimizerDuality.pressureValue_congr_ae he, pressureValue_uniform_spectral]⟩

/-- **Proposition 5.1, inequality** (`eq:spectral-d12-base`, first half): for every finite-entropy
probability density `ρ` on `𝕋¹²`, `(2π)^12 ‖ρ‖²_{Ḣ^{-6}} ≤ 2 Ent ρ`, the energy being the extended
nonnegative sum `spectralEnergy ρ = ∑_{k≠0}|k|^{-12}|ρ̂(k)|²`. -/
theorem spectralD12Inequality (hsc : ScalarBounds) : SpectralD12Inequality := by
  intro g hg
  obtain ⟨ρ₀, hρ₀, hz⟩ := exists_zero_minimizer hsc
  have h := hρ₀.2 g hg
  rw [hz, pressureValue_spectral (by norm_num) g hg] at h
  have h' : (1 / 2 : ℝ) * (∑' k, spectralTerm g k) - entropy g ≤ 0 := by exact_mod_cast h
  rw [spectralEnergy_eq_ofReal (by norm_num) g hg]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Proposition 5.1, equality case** (`eq:spectral-d12-base`, second half): equality forces
`ρ = 1` almost everywhere (every equality density is a global minimizer, hence uniform). -/
theorem spectralD12Equality (hsc : ScalarBounds) : SpectralD12Equality := by
  intro g hg heq
  obtain ⟨ρ₀, hρ₀, hz⟩ := exists_zero_minimizer hsc
  rw [spectralEnergy_eq_ofReal (by norm_num) g hg,
    ENNReal.ofReal_eq_ofReal_iff (spectralTerm_tsum_nonneg g)
      (mul_nonneg (by norm_num) (entropy_nonneg g hg))] at heq
  have hg0 : pressureValue (spectralThreshold 12) g = 0 := by
    rw [pressureValue_spectral (by norm_num) g hg, heq]
    have h0 : (1 / 2 : ℝ) * (2 * entropy g) - entropy g = 0 := by ring
    rw [h0]
    rfl
  have hgmin : IsGlobalMinimizer (spectralThreshold 12) g :=
    ⟨hg, fun s hs => by rw [hg0, ← hz]; exact hρ₀.2 s hs⟩
  exact minimizer_uniform hsc g hgmin

/-- **Proposition 5.1** (both halves). -/
theorem spectral_d12_base (hsc : ScalarBounds) (ρ : ProbabilityDensity 12) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔ ρ.value =ᵐ[torusMeasure 12] fun _ => 1) :=
  ⟨spectralD12Inequality hsc ρ hρ,
    ⟨spectralD12Equality hsc ρ hρ, fun h => by
      have he : ρ.value =ᵐ[torusMeasure 12] (uniformDensity 12).value := h
      have hpv : pressureValue (spectralThreshold 12) ρ = 0 := by
        rw [OptimizerDuality.pressureValue_congr_ae he, pressureValue_uniform_spectral]
      rw [pressureValue_spectral (by norm_num) ρ hρ] at hpv
      have h0 : (1 / 2 : ℝ) * (∑' k, spectralTerm ρ k) - entropy ρ = 0 := by exact_mod_cast hpv
      rw [spectralEnergy_eq_ofReal (by norm_num) ρ hρ]
      congr 1
      linarith⟩⟩

/-! ### Proposition 5.7 and Corollary 5.8 -/

/-- The dimension-twelve inequality and equality case, supplied to the dimension transfer
(Proposition 5.7, `Transfer.spectral_dimension_transfer`): for every `d ≥ 12` and every
finite-entropy density on `𝕋^d`, the inequality, and equality exactly for `ρ = 1`. -/
theorem spectral_high_density (hsc : ScalarBounds) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy) :
    spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
      (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
        ρ.value =ᵐ[torusMeasure d] fun _ => 1) :=
  Transfer.spectral_dimension_transfer (spectralD12Inequality hsc) (spectralD12Equality hsc) hd ρ hρ

/-- **Extended inequality** `(2π)^d ‖ρ‖²_{Ḣ^{-d/2}} ≤ 2 Ent ρ` in `[0,∞]` for every probability
density, finite or infinite entropy (`Ent ρ = +∞` when the entropy is infinite;
`Vocab.torusEntropy` is the extended-valued entropy). -/
theorem spectral_high_extended (hsc : ScalarBounds) {d : ℕ} (hd : 12 ≤ d)
    (ρ : ProbabilityDensity d) :
    spectralEnergy ρ ≤ 2 * Vocab.torusEntropy ρ.value := by
  by_cases hρ : ρ.FiniteEntropy
  · rw [Vocab.torusEntropy_density_eq_ofReal_entropy ρ hρ,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact (spectral_high_density hsc hd ρ hρ).1
  · rw [Vocab.torusEntropy_density_eq_top ρ hρ]
    simp

/-- **Corollary 5.8 (`cor:section5-high-endpoint`).**  For every `d ≥ 12`:
(a) the density inequality `Ent ≥ (2π)^d/2 ‖ρ‖²_{Ḣ^{-d/2}}` with equality only for `ρ = 1`;
(b) the dual potential inequality with coefficient `A_s(d)` on the full critical Sobolev space, with
equality only for constants; (c) `β_gm(d) = β_s(d)`, the zero-pressure set having maximum `β_s(d)`;
and the sharp coefficient `A_s(d)` as the least `A > 0` with `C_d(A) = 0`. -/
theorem high_endpoint (hsc : ScalarBounds) {d : ℕ} (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
        (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ∧
        (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    IsGreatest {β : ℝ | 0 ≤ β ∧ pressure d β = 0} (spectralThreshold d) ∧
    VariationalCurves.globalTransition d = spectralThreshold d ∧
    IsLeast {A : ℝ | 0 < A ∧ coefficientDefect d A = 0} (spectralCoefficient d) := by
  have h12 := spectralD12Inequality hsc
  have hEq := spectralD12Equality hsc
  have hME : CosineMixtureTransfer.MixtureEndpoint 12 :=
    CosineMixtureTransfer.mixture_endpoint_of_density (by norm_num) h12
  have hthr := pressure_threshold_from_twelve hME hd
  refine ⟨fun ρ hρ => spectral_high_density hsc hd ρ hρ, fun u hu => ?_, hthr, ?_,
    coefficient_threshold_from_twelve hME hd⟩
  · obtain ⟨hi, hle⟩ := potential_endpoint_from_twelve hME hd u hu
    exact ⟨hi, hle, potential_rigidity_from_twelve hME (Transfer.mixtureRigidity_twelve h12 hEq) hd u hu⟩
  · exact hthr.csSup_eq

end BecknerOnofri.V2.Assembly
