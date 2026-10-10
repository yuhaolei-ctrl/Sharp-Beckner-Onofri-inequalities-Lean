module

public import BecknerOnofri.V2.Section3.Written

@[expose] public section

/-! # S024, step 1: the Section 3 mixture-gap mechanism, parametrized by the scalar margin

`BecknerOnofri.V2.Section3.mixture_energy_gap` (`2 ≤ d ≤ 10`) is the chain
`index_scalar → component_scalar → finite_mixture_gap → mixture_energy_gap`, in which the only
dimension-dependent input is the scalar inequality of Proposition 3.4 with the margin `3/1100` and the
coupling `2 · endpointConstant d = 2d/β_s(d)`.  Here the same four steps are carried out with the
coupling constant `c > 0` and the scalar margin `g ≥ 0` as parameters, the scalar input being the
explicit hypothesis

  `ScalarGap d c g : ∀ n, c · G_{d,n} + g · 1_{n ≥ 1} ≤ d · H_n`

(`G_{d,n} = GaussianLattice.binomialEnergy d n`, `H_n = harmonic n`), which is the scalar
statement of the manuscript (`eq:scalar-result` for `d ≤ 10`; `d11:eq:gap` for `d = 11`).
The statement of the conclusion has the same shape as `mixture_energy_gap`.  The theorem
`mixture_energy_gap_via_param` re-derives `mixture_energy_gap` from the parametrized version. -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.ElevenBounds
open BecknerOnofri.HighDim BecknerOnofri.V2.Section3
open Legacy.D10 (latentBox latentWeight latentWeight_nonneg)
open Legacy.TorusEndpoint (densityFourier)
open Legacy.BecknerOnofri

variable {d : ℕ}

/-- The scalar hypothesis of the mixture argument, with coupling `c` and margin `g`:
`c · G_{d,n} + g · 1_{n ≥ 1} ≤ d · H_n` for every `n`. -/
def ScalarGap (d : ℕ) (c g : ℝ) : Prop :=
  ∀ n : ℕ, c * GaussianLattice.binomialEnergy d n + g * (if 1 ≤ n then (1 : ℝ) else 0) ≤
    (d : ℝ) * ((harmonic n : ℚ) : ℝ)

/-- Proposition 3.4 + `eq:mixed-index-average` for one index vector `L`, parametrized:
`c G_d(L) + (g/d) #{i : L_i ≥ 1} ≤ ∑_i H_{L_i}`. -/
theorem component_scalar_param (hd0 : 0 < d) {c g : ℝ} (hc : 0 ≤ c) (hS : ScalarGap d c g)
    (L : Fin d → ℕ) :
    c * (∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
          RandomRectangles.componentCoeff L k) +
      (g / (d : ℝ)) * ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) ≤
      ∑ i, ((harmonic (L i) : ℚ) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hcomp := MixedBinomialComparison.componentEnergy_le_average_diagonal hd0 L
  have hE : (∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
      RandomRectangles.componentCoeff L k) = CosineMixtureEnergy.componentEnergy L := rfl
  rw [hE]
  calc _ ≤ c * ((1 / (d : ℝ)) * ∑ i, GaussianLattice.binomialEnergy d (L i)) +
        (g / (d : ℝ)) * ∑ i, (if 1 ≤ L i then (1 : ℝ) else 0) := by gcongr
    _ = ∑ i, ((c * GaussianLattice.binomialEnergy d (L i) +
          g * (if 1 ≤ L i then (1 : ℝ) else 0)) / (d : ℝ)) := by
        simp only [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i _ => ?_
        field_simp
    _ ≤ _ := sum_le_sum fun i _ => by
        rw [div_le_iff₀ hdR]
        linarith [hS (L i)]

/-- **Finite mixtures, parametrized form of `eq:mixture-strict-entropy-gap`** (the analogue of
`Section3.finite_mixture_gap`): for finitely many components with arbitrary nonnegative weights,
`c ∑_{k} w(k) |ρ̂(k)|² + (g/d) · posMass ≤ 2 ∑_i ∑_{j ≥ 1} |ρ̂(j e_i)|² / j`. -/
theorem finite_mixture_gap_param (hd0 : 0 < d) {c g : ℝ} (hc : 0 ≤ c) (hS : ScalarGap d c g)
    {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin d → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    c * (∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
          ‖densityFourier (CosineMixture.mixture s w N) k‖ ^ 2) +
      (g / (d : ℝ)) * posMass s w N ≤
      2 * ∑ i : Fin d, ∑' j : ℕ, ‖densityFourier (CosineMixture.mixture s w N)
        (Pi.single i ((j : ℤ) + 1))‖ ^ 2 / ((j : ℝ) + 1) := by
  have hE : (∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
      ‖densityFourier (CosineMixture.mixture s w N) k‖ ^ 2) =
      latAvg s w N (fun L => ∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
          RandomRectangles.componentCoeff L k) :=
    CosineMixtureTransfer.weighted_mixture_tsum s w N _
  rw [hE, posMass, ← latAvg_mul, ← latAvg_mul, ← latAvg_add]
  calc _ ≤ latAvg s w N (fun L => ∑ i, ((harmonic (L i) : ℚ) : ℝ)) :=
        latAvg_mono s w N hw (fun L => component_scalar_param hd0 hc hS L)
    _ = ∑ i, latAvg s w N (fun L => ((harmonic (L i) : ℚ) : ℝ)) := latAvg_sum s w N _ _
    _ = _ := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => latAvg_harmonic s w N i

/-- **The mixture energy-entropy inequality with gap, parametrized** (the analogue of
`Section3.mixture_energy_gap`, for any `d ≥ 1`, coupling `c > 0` and margin `g ≥ 0` for which the
scalar hypothesis `ScalarGap d c g` holds).  `γ` is any lower bound for the eventual latent
positive-index mass. -/
theorem mixture_energy_gap_param (hd0 : 0 < d) {c g : ℝ} (hc : 0 < c) (hg : 0 ≤ g)
    (hS : ScalarGap d c g) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N)
    (γ : ℝ) (hγ : ∀ᶠ m in atTop, γ ≤ posMass (range m) w N) :
    spectralEnergy ρ ≠ ⊤ ∧
      c * (spectralEnergy ρ).toReal + (g / (d : ℝ)) * γ ≤ 2 * entropy ρ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hs : Summable w := hm.summable
  obtain ⟨hsum, hA⟩ := axis_marginal_bound hd0 ρ hρ
  set A : ℝ := ∑ i : Fin d, ∑' j, axisTerm ρ i j with hAdef
  have hgd : 0 ≤ g / (d : ℝ) := div_nonneg hg hdR.le
  have hax (i : Fin d) (j : ℕ) : axisTerm ρ i j =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 1))‖ ^ 2 /
        ((j : ℝ) + 1) := by
    unfold axisTerm
    rw [BecknerOnofri.V2.Rearrangement.fourierCoeff_congr_ae' he]
    rfl
  -- the partial bound
  have hpart (m : ℕ) :
      c * (∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
            ‖densityFourier (CosineMixture.mixture (range m) w N) k‖ ^ 2) +
        (g / (d : ℝ)) * posMass (range m) w N ≤ 2 * A := by
    refine (finite_mixture_gap_param hd0 hc.le hS (range m) w N (fun a _ => hw a)).trans ?_
    have hi (i : Fin d) : ∑' j : ℕ, ‖densityFourier (CosineMixture.mixture (range m) w N)
        (Pi.single i ((j : ℤ) + 1))‖ ^ 2 / ((j : ℝ) + 1) ≤ ∑' j, axisTerm ρ i j := by
      have hle (j : ℕ) : ‖densityFourier (CosineMixture.mixture (range m) w N)
          (Pi.single i ((j : ℤ) + 1))‖ ^ 2 / ((j : ℝ) + 1) ≤ axisTerm ρ i j := by
        rw [hax]
        exact div_le_div_of_nonneg_right (fourier_sq_partial_le w N hw hs m _) (by positivity)
      exact Summable.tsum_le_tsum hle
        (Summable.of_nonneg_of_le (fun j => div_nonneg (sq_nonneg _) (by positivity)) hle (hsum i))
        (hsum i)
    have := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin d))) => hi i)
    linarith
  have hsw : ∀ k : Fin d → ℤ, 0 ≤ GaussianLattice.spectralWeight k := spectralWeight_nonneg'
  obtain ⟨m1, hm1⟩ := hγ.exists
  have hE1 : 0 ≤ ∑' k : Fin d → ℤ, GaussianLattice.spectralWeight k *
      ‖densityFourier (CosineMixture.mixture (range m1) w N) k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (hsw k) (sq_nonneg _)
  have hBnn : 0 ≤ (2 * A - (g / (d : ℝ)) * γ) / c := by
    apply div_nonneg _ hc.le
    have := hpart m1
    nlinarith [mul_le_mul_of_nonneg_left hm1 hgd, mul_nonneg hc.le hE1]
  have hC : ∀ᶠ m in atTop, CosineMixtureTransfer.weightedEnergyENN
      GaussianLattice.spectralWeight (CosineMixture.mixture (range m) w N) ≤
      ENNReal.ofReal ((2 * A - (g / (d : ℝ)) * γ) / c) := by
    filter_upwards [hγ] with m hmγ
    rw [CosineMixtureTransfer.finite_weightedEnergyENN (range m) w N _ hsw]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hc]
    have := hpart m
    nlinarith [mul_le_mul_of_nonneg_left hmγ hgd]
  have hbound := weightedEnergyENN_le_of_eventually w N hw hs _ _ hC
  have hspec : spectralEnergy ρ = CosineMixtureTransfer.weightedEnergyENN
      GaussianLattice.spectralWeight (CosineMixtureApproximation.rho w N) :=
    (spectralEnergy_eq_weightedEnergyENN hd0 ρ).trans (weightedEnergyENN_congr_ae' _ he)
  rw [← hspec] at hbound
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound, ?_⟩
  have hreal := ENNReal.toReal_le_of_le_ofReal hBnn hbound
  rw [le_div_iff₀ hc] at hreal
  linarith [hA]

/-! ### The case `2 ≤ d ≤ 10` is the instance `c = 2 d/β_s(d)`, `g = 3/1100` -/

/-- Proposition 3.4 in the form `ScalarGap d (2 · endpointConstant d) (3/1100)`. -/
theorem scalarGap_low (hd2 : 2 ≤ d) (hd10 : d ≤ 10) :
    ScalarGap d (2 * endpointConstant d) (3 / 1100) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  intro n
  have h := index_scalar hd2 hd10 n
  have h2 : (2 * endpointConstant d * (1 / (d : ℝ)) *
      GaussianLattice.binomialEnergy d n + 3 / (1100 * (d : ℝ)) * (if 1 ≤ n then (1 : ℝ) else 0)) *
      (d : ℝ) = 2 * endpointConstant d * GaussianLattice.binomialEnergy d n +
        3 / 1100 * (if 1 ≤ n then (1 : ℝ) else 0) := by
    field_simp
  rw [← h2, mul_comm (d : ℝ)]
  exact mul_le_mul_of_nonneg_right h hd0.le

/-- `Section3.mixture_energy_gap` is recovered from the parametrized theorem (same statement). -/
theorem mixture_energy_gap_via_param (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N)
    (γ : ℝ) (hγ : ∀ᶠ m in atTop, γ ≤ posMass (range m) w N) :
    spectralEnergy ρ ≠ ⊤ ∧
      2 * endpointConstant d * (spectralEnergy ρ).toReal +
        (3 / (1100 * (d : ℝ))) * γ ≤ 2 * entropy ρ := by
  have hd0 : 0 < d := by omega
  have hc : 0 < 2 * endpointConstant d := by
    unfold endpointConstant
    have : 0 < Legacy.TorusEndpoint.endpointSigma d := Vocab.spectralThreshold_pos' hd0
    positivity
  have h := mixture_energy_gap_param hd0 hc (by norm_num) (scalarGap_low hd2 hd10) ρ hρ w N hw hm
    he γ hγ
  rwa [show (3 / 1100 : ℝ) / (d : ℝ) = 3 / (1100 * (d : ℝ)) by
    rw [div_div]] at h

end BecknerOnofri.V2.Reaudit.ElevenBounds
