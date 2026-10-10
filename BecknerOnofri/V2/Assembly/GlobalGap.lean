module

public import BecknerOnofri.V2.Assembly.CountForm
public import BecknerOnofri.V2.Channel.Prop512
public import BecknerOnofri.V2.Channel.CountLaw
public import BecknerOnofri.V2.Mixture.Countable
public import BecknerOnofri.V2.Reaudit.Mixtures.CountableTail
public import BecknerOnofri.V2.Reaudit.SpinChannel.Prop512Joint
public import BecknerOnofri.SpinCubeEnergy
public import BecknerOnofri.EntropyEnergySpectral
public import BecknerOnofri.EntropyMixtureRigidity

@[expose] public section

/-!
# Proposition 5.10 (`prop:section5-global-entropy-gap`), work package G14

For a smooth strictly positive probability density `ρ` on `𝕋¹²`, invariant under coordinate
permutations, of the form `eq:mixture`, with `log ρ = V(cos 2πx_1, …, cos 2πx_12)`, `V ∈ C^∞([-1,1]^12)`,
`∂_iV ≥ 0`, `∂_i²V ≥ 0`:

`Ent(ρ) - ½ Σ_{k≠0} |k|^{-12} |ρ̂(k)|² ≥ ρ̂(e_1)⁴/250`  (and the stronger internal constant `1/70`),
`ρ̂(e_1) ≥ 0`, and `ρ̂(e_1) = 0` implies `ρ = 1`.

The proof is the written one: subtract Proposition 5.11 (`Mixture.singular_fourier_tail`, the
singular Fourier tail) from Proposition 5.12(i) (`Channel.spin_entropy_comparison_i`), identify the
energy in the cube `{-1,0,1}^12` with the weighted sum of squared joint spin moments
(`Spin.cube_half_energy_eq_quadratic`, `eq:section5-global-cube-energy`; the term-by-term cancellation
of the coefficients `1/40, 2/15, 27/40` is the matching of the two sums in Propositions 5.11 and
5.12(i)), and apply Proposition 5.12(ii) (`count_form_public` / `count_form_internal`, via the
measure-form deduction `spin_final_ii`) to the spin law `ν_ρ`.

The scalar bounds of Lemma 5.21 enter only through `hsc : ScalarBounds`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators ContDiff
namespace BecknerOnofri.V2.Assembly
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.V2.Channel
  BecknerOnofri.V2.FiniteState
open BecknerOnofri.V2.ThetaTail (cube12 latticeNorm)
open BecknerOnofri.HighDim.Spin (channelLaw Exchangeable jointSpin countLaw)

/-! ### Proposition 5.12(ii), measure form, with an arbitrary constant -/

/-- Deduction of the measure form of Proposition 5.12(ii) from its count form, with an arbitrary
constant `c` in place of `1/250` (the same proof as `Channel.spin_final_of_count_form`). -/
theorem spin_final_ii (c : ℝ)
    (hcount : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ p : Spin.Count → ℝ, Spin.FeasibleAt t p →
      c * t ^ 4 ≤ Spin.functional p + 12 * BecknerOnofri.V2.Circle.psi t)
    {ν : Spin.Configuration → ℝ} (hν : Exchangeable ν) (hnn : ∀ σ, 0 ≤ ν σ)
    (hmass : (∑ σ, ν σ) = 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i : Fin 12, (∑ σ : Spin.Configuration, ν σ * jointSpin {i} σ) = t)
    (hcap : ν ∅ ≤ 1 / 4096) :
    c * t ^ 4 ≤
      2 * (∑ σ : Spin.Configuration, ν σ * Real.log (ν σ / (1 / 4096))) -
        (∑ r ∈ Finset.Icc 1 12, ((12 : ℕ).choose r : ℝ) * 2 ^ (r - 1) / (r : ℝ) ^ 6 *
          (∑ σ : Spin.Configuration, ν σ * jointSpin (firstR r) σ) ^ 2) +
        12 * BecknerOnofri.V2.Circle.psi t := by
  have hfeas : Spin.FeasibleAt t (countLaw ν) :=
    ⟨feasible_countLaw hnn hmass hcap, by rw [mean_countLaw_eq hν 0, hmean 0]⟩
  have h := hcount t ht (countLaw ν) hfeas
  rw [relativeEntropy_eq_count hν, printed_energy_eq_quadratic hν]
  unfold Spin.functional at h
  linarith

/-! ### Mixture facts -/

theorem hasPositiveMixture (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hmix : IsCountableCosineMixture ρ) :
    GenericCosineRepresentation.HasPositiveCosineMixture ρ.value := by
  obtain ⟨w, N, hw, hm, he⟩ := hmix
  have hc := UniformFourier.smooth_continuous hs
  have he' : ρ.value =ᵐ[torusMeasure 12] Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  exact ⟨w, N, hw, hm,
    CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value hc w N hw hm.summable he',
    CosineMixtureTransfer.mixture_eq_of_continuous ρ.value hc w N hw hm.summable he'⟩

/-- `0 ≤ ρ̂(e_1) ≤ 1` for a smooth cosine mixture. -/
theorem firstCoefficient_mem_Icc (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hmix : IsCountableCosineMixture ρ) : firstCoefficient ρ ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨w, N, hw, hm, hSup, he⟩ := hasPositiveMixture ρ hs hmix
  unfold firstCoefficient
  rw [he]
  change (Legacy.TorusEndpoint.densityFourier (Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N)
    (Pi.single (0 : Fin 12) (1 : ℤ))).re ∈ Icc (0 : ℝ) 1
  rw [CosineMixtureTransfer.rho_fourier w N hw hm.summable, Complex.ofReal_re]
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  · have hsum := CosineMixtureTransfer.summable_mixture_coeff w N hw hm.summable
      (Pi.single (0 : Fin 12) (1 : ℤ))
    have hle := hsum.tsum_le_tsum (fun n => mul_le_of_le_one_right (hw n)
      (CosineMixtureTransfer.componentCoeff_le_one _ _)) hm.summable
    exact hle.trans_eq hm.tsum_eq

/-! ### Proposition 5.10 -/

theorem count_form_public' (hsc : ScalarBounds) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ p : Spin.Count → ℝ, Spin.FeasibleAt t p →
      (1 / 250 : ℝ) * t ^ 4 ≤ Spin.functional p + 12 * BecknerOnofri.V2.Circle.psi t := by
  intro t ht p hp
  have := count_form_public hsc t ht p hp
  linarith

/-- The common assembly, for an arbitrary constant `c` in the count form. -/
theorem global_gap_of_count (c : ℝ)
    (hcount : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ p : Spin.Count → ℝ, Spin.FeasibleAt t p →
      c * t ^ 4 ≤ Spin.functional p + 12 * BecknerOnofri.V2.Circle.psi t)
    (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value) (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (cosineVector x))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (h2 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i (cosinePartial i V) v) :
    c * firstCoefficient ρ ^ 4 ≤ entropy ρ - (1 / 2 : ℝ) * EntropyTail.fullFourierEnergy ρ.value := by
  have hc : Continuous ρ.value := UniformFourier.smooth_continuous hs
  have hmixP := hasPositiveMixture ρ hs hmix
  obtain ⟨⟨hex, hnn, hmass, -, hmean⟩, hcap, -, hent⟩ :=
    Reaudit.SpinChannel.spin_entropy_comparison_i_joint ρ hs hp hperm hmix V hV hlog h1 h2
  have ht := firstCoefficient_mem_Icc ρ hs hmix
  have hfinal := spin_final_ii c hcount hex hnn hmass ht hmean hcap
  have hcube := Spin.cube_half_energy_eq_quadratic ρ hmixP hex
  have hsplit := EntropyTail.fullFourierEnergy_split hc
  have htail := BecknerOnofri.V2.Reaudit.Mixtures.singular_fourier_tail_direct ρ hs hmix
  have hT : (∑' k : Frequency 12, EntropyTail.scalarTailWeight k * ‖fourierCoeff ρ.value k‖ ^ 2) =
      ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
        (fun k => (latticeNorm k ^ 12)⁻¹ * ‖HighDim.fourierCoeff ρ.value k‖ ^ 2) k :=
    tsum_congr (fun k => Mixture.tailWeight_mul_eq_indicator k _)
  rw [printed_energy_eq_quadratic hex] at hfinal
  unfold spinRelEntropy at hent
  rw [← hT] at htail
  linarith

/-- **Proposition 5.10 with the internal constant `1/70`.** -/
theorem global_entropy_gap_internal (hsc : ScalarBounds)
    (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value) (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (cosineVector x))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (h2 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i (cosinePartial i V) v) :
    firstCoefficient ρ ^ 4 / 70 ≤ entropy ρ - (1 / 2 : ℝ) * EntropyTail.fullFourierEnergy ρ.value := by
  have := global_gap_of_count (1 / 70)
    (fun t ht p hp => by
      have := count_form_internal hsc ht.1 ht.2 hp
      change t ^ 4 / 70 ≤ _ at this
      have e : BecknerOnofri.V2.Circle.psi t = psiV2 t := rfl
      rw [e]; linarith)
    ρ hs hp hperm hmix V hV hlog h1 h2
  linarith

/-- `ρ̂(e_i) = ρ̂(e_1)` for a coordinate-permutation invariant density, as the integral
`∫ ρ cos(2π x_i)`; hence the vanishing of `ρ̂(e_1)` kills every axis coefficient. -/
theorem axis_coefficient_eq_zero (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value)
    (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (cosineVector x))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (h2 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i (cosinePartial i V) v)
    (hz : firstCoefficient ρ = 0) (i : Fin 12) :
    Legacy.TorusEndpoint.densityFourier ρ.value (axisFrequency i) = 0 := by
  have hc : Continuous ρ.value := UniformFourier.smooth_continuous hs
  obtain ⟨⟨-, -, -, -, hmean⟩, -, -, -⟩ :=
    Reaudit.SpinChannel.spin_entropy_comparison_i_joint ρ hs hp hperm hmix V hV hlog h1 h2
  have hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x)) :=
    fun x => by rw [← hlog x, Real.exp_log (hp x)]
  have heven := rep_even hrep
  have hmi := hmean i
  rw [Spin.channelLaw_joint_moment] at hmi
  simp only [Finset.prod_singleton] at hmi
  have hre : (HighDim.fourierCoeff ρ.value (Pi.single i (1 : ℤ))).re = 0 := by
    rw [fourierCoeff_axis_re hc i 1, hmi, hz]
  have him := fourierCoeff_even_im heven (Pi.single i (1 : ℤ))
  have he : (axisFrequency i : Frequency 12) = Pi.single i (1 : ℤ) := by
    ext j
    simp [axisFrequency, Pi.single_apply]
  rw [he]
  exact Complex.ext hre him

/-- **Proposition 5.10 (`prop:section5-global-entropy-gap`), as printed, with the public constant
`1/250`.**  Under the printed hypotheses (smooth strictly positive probability density on `𝕋¹²`,
permutation invariant, of the form `eq:mixture`, `log ρ = V(cos 2πx)` with `V ∈ C^∞([-1,1]^12)`,
`∂_iV ≥ 0`, `∂_i²V ≥ 0`),
`Ent(ρ) - ½ Σ_{k≠0} |k|^{-12}|ρ̂(k)|² ≥ ρ̂(e_1)⁴/250`; moreover `ρ̂(e_1) ≥ 0`, and
`ρ̂(e_1) = 0` implies `ρ = 1`.  (`fullFourierEnergy ρ.value = Σ_{k≠0} |k|^{-12}|ρ̂(k)|²`
`= (2π)^12 ‖ρ‖²_{Ḣ^{-6}}`; `EntropyTail.spectralEnergy_eq_fullFourierEnergy`.) -/
theorem global_entropy_gap (hsc : ScalarBounds)
    (ρ : ProbabilityDensity 12) (hs : SmoothOnTorus ρ.value) (hp : ∀ x, 0 < ρ.value x)
    (hperm : ∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12), ρ.value (fun i => x (π i)) = ρ.value x)
    (hmix : IsCountableCosineMixture ρ)
    (V : (Fin 12 → ℝ) → ℝ) (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (hlog : ∀ x, Real.log (ρ.value x) = V (cosineVector x))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (h2 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i (cosinePartial i V) v) :
    firstCoefficient ρ ^ 4 / 250 ≤
        entropy ρ - (1 / 2 : ℝ) * EntropyTail.fullFourierEnergy ρ.value ∧
      0 ≤ firstCoefficient ρ ∧ (firstCoefficient ρ = 0 → ρ.value = fun _ => 1) := by
  refine ⟨?_, (firstCoefficient_mem_Icc ρ hs hmix).1, fun hz => ?_⟩
  · have := global_gap_of_count (1 / 250) (count_form_public' hsc) ρ hs hp hperm hmix V hV hlog h1 h2
    linarith
  · exact EntropyMixtureRigidity.positive_mixture_uniform (hasPositiveMixture ρ hs hmix)
      (axis_coefficient_eq_zero ρ hs hp hperm hmix V hV hlog h1 h2 hz)

end BecknerOnofri.V2.Assembly
