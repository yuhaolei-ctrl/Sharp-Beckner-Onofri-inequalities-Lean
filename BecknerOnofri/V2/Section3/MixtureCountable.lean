module

public import BecknerOnofri.V2.Section3.MixtureFinite
public import BecknerOnofri.MixtureEnergyStatementBridge
public import BecknerOnofri.V2.Reaudit.Mixtures.ChainRule

@[expose] public section

/-! # The written mixture derivation, countable stage (G04)

Passage from finite to countably infinite cosine-power mixtures *without* any majorant hypothesis
(`hSup`): the Fourier coefficients of the partial sums increase to those of the full mixture, so the
extended-real energies are suprema of the partial energies (the manuscript's "directly by
nonnegativity of the sums"). -/

noncomputable section
open Finset Filter MeasureTheory
open scoped BigOperators ENNReal Topology

namespace BecknerOnofri.V2.Section3
open BecknerOnofri.HighDim
open Legacy.TorusEndpoint (densityFourier)

variable {d : ℕ}

open Legacy.BecknerOnofri

/-- Monotone convergence for the energy of a countable mixture, in the form with an eventual
bound. -/
theorem weightedEnergyENN_le_of_eventually {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (g : (Fin d → ℤ) → ℝ) (C : ℝ≥0∞)
    (hb : ∀ᶠ m in atTop, CosineMixtureTransfer.weightedEnergyENN g
      (CosineMixture.mixture (range m) w N) ≤ C) :
    CosineMixtureTransfer.weightedEnergyENN g (CosineMixtureApproximation.rho w N) ≤ C := by
  unfold CosineMixtureTransfer.weightedEnergyENN
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  have hpoint (k : Fin d → ℤ) : Tendsto (fun m =>
      ENNReal.ofReal (g k * ‖densityFourier (CosineMixture.mixture (range m) w N) k‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (g k * ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2))) := by
    simp only [CosineMixture.mixture_fourier, CosineMixtureTransfer.rho_fourier w N hw hs,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hc := (CosineMixtureTransfer.summable_mixture_coeff w N hw hs k).hasSum.tendsto_sum_nat
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hc.pow 2).const_mul (g k))
  apply le_of_tendsto (tendsto_finsetSum S (fun k _ => hpoint k))
  filter_upwards [hb] with m hm
  exact (ENNReal.sum_le_tsum S).trans hm

theorem fourier_sq_partial_le (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) (m : ℕ) (k : Fin d → ℤ) :
    ‖densityFourier (CosineMixture.mixture (range m) w N) k‖ ^ 2 ≤
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2 := by
  simp only [CosineMixture.mixture_fourier, CosineMixtureTransfer.rho_fourier w N hw hs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : 0 ≤ ∑ n ∈ range m, w n * BecknerOnofri.RandomRectangles.componentCoeff (N n) k :=
    sum_nonneg (fun n _ => mul_nonneg (hw n) (BecknerOnofri.RandomRectangles.componentCoeff_nonneg _ _))
  have hle := (CosineMixtureTransfer.summable_mixture_coeff w N hw hs k).sum_le_tsum (range m)
    (fun n _ => mul_nonneg (hw n) (BecknerOnofri.RandomRectangles.componentCoeff_nonneg _ _))
  exact (sq_le_sq₀ hp (hp.trans hle)).mpr hle

theorem sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast x n, ← Real.rpow_mul hx,
    ← Real.rpow_natCast (x ^ (1 / 2 : ℝ)) n, ← Real.rpow_mul hx]
  congr 1
  ring

theorem spectralWeight_eq_weight (hd : 0 < d) (k : Fin d → ℤ) :
    Legacy.BecknerOnofri.GaussianLattice.spectralWeight k = RectangleLattice.weight (d : ℝ) k := by
  rw [CosineMixtureTransfer.weight_nat_exponent_eq hd k]
  unfold Legacy.BecknerOnofri.GaussianLattice.spectralWeight
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    rw [one_div]
    congr 1
    unfold HighDim.frequencyLength
    exact sqrt_pow_eq _ (Finset.sum_nonneg fun j _ => sq_nonneg _) d

theorem spectralWeight_nonneg' (k : Fin d → ℤ) :
    0 ≤ Legacy.BecknerOnofri.GaussianLattice.spectralWeight k :=
  Legacy.BecknerOnofri.GaussianLattice.spectralWeight_nonneg k

theorem weightedEnergyENN_congr_ae' (g : (Fin d → ℤ) → ℝ) {f h : Torus d → ℝ}
    (he : f =ᵐ[torusMeasure d] h) :
    CosineMixtureTransfer.weightedEnergyENN g f = CosineMixtureTransfer.weightedEnergyENN g h := by
  have hc (k : Fin d → ℤ) : densityFourier f k = densityFourier h k :=
    integral_congr_ae (he.mono (fun x hx => by dsimp only; rw [hx]))
  unfold CosineMixtureTransfer.weightedEnergyENN
  simp_rw [hc]

theorem spectralEnergy_eq_weightedEnergyENN (hd : 0 < d) (ρ : ProbabilityDensity d) :
    spectralEnergy ρ = CosineMixtureTransfer.weightedEnergyENN
      Legacy.BecknerOnofri.GaussianLattice.spectralWeight ρ.value := by
  have h : (Legacy.BecknerOnofri.GaussianLattice.spectralWeight : (Fin d → ℤ) → ℝ) =
      RectangleLattice.weight (d : ℝ) := funext (spectralWeight_eq_weight hd)
  rw [h, CosineMixtureTransfer.weightedEnergyENN_eq_inversePowerEnergy hd]
  rfl

/-- **The mixture energy-entropy inequality with gap, for every finite-entropy countable
cosine-power mixture** (`eq:mixture-strict-entropy-gap` of the manuscript, before specialising `γ`).
`γ` is any lower bound for the eventual latent positive-index mass. -/
theorem mixture_energy_gap (hd2 : 2 ≤ d) (hd10 : d ≤ 10) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1)
    (he : ρ.value =ᵐ[torusMeasure d] CosineMixtureApproximation.rho w N)
    (γ : ℝ) (hγ : ∀ᶠ m in atTop, γ ≤ posMass (range m) w N) :
    spectralEnergy ρ ≠ ⊤ ∧
      2 * Legacy.BecknerOnofri.endpointConstant d * (spectralEnergy ρ).toReal +
        (3 / (1100 * (d : ℝ))) * γ ≤ 2 * entropy ρ := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hs : Summable w := hm.summable
  obtain ⟨hsum, hA⟩ := BecknerOnofri.V2.Reaudit.Mixtures.axis_marginal_bound_chain hd0 ρ hρ
  set A : ℝ := ∑ i : Fin d, ∑' j, axisTerm ρ i j with hAdef
  have hc : 0 < 2 * Legacy.BecknerOnofri.endpointConstant d := by
    unfold Legacy.BecknerOnofri.endpointConstant
    have : 0 < Legacy.TorusEndpoint.endpointSigma d := Vocab.spectralThreshold_pos' hd0
    positivity
  have hg : 0 < 3 / (1100 * (d : ℝ)) := by positivity
  have hax (i : Fin d) (j : ℕ) : axisTerm ρ i j =
      ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 1))‖ ^ 2 /
        ((j : ℝ) + 1) := by
    unfold axisTerm
    rw [BecknerOnofri.V2.Rearrangement.fourierCoeff_congr_ae' he]
    rfl
  -- the partial bound
  have hpart (m : ℕ) :
      2 * Legacy.BecknerOnofri.endpointConstant d *
          (∑' k : Fin d → ℤ, Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
            ‖densityFourier (CosineMixture.mixture (range m) w N) k‖ ^ 2) +
        (3 / (1100 * (d : ℝ))) * posMass (range m) w N ≤ 2 * A := by
    refine (finite_mixture_gap hd2 hd10 (range m) w N (fun a _ => hw a)).trans ?_
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
  have hsw : ∀ k : Fin d → ℤ, 0 ≤ Legacy.BecknerOnofri.GaussianLattice.spectralWeight k :=
    spectralWeight_nonneg'
  obtain ⟨m1, hm1⟩ := hγ.exists
  have hE1 : 0 ≤ ∑' k : Fin d → ℤ, Legacy.BecknerOnofri.GaussianLattice.spectralWeight k *
      ‖densityFourier (CosineMixture.mixture (range m1) w N) k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (hsw k) (sq_nonneg _)
  have hBnn : 0 ≤ (2 * A - 3 / (1100 * (d : ℝ)) * γ) / (2 * Legacy.BecknerOnofri.endpointConstant d) := by
    apply div_nonneg _ hc.le
    have := hpart m1
    nlinarith [mul_le_mul_of_nonneg_left hm1 hg.le, mul_nonneg hc.le hE1]
  have hC : ∀ᶠ m in atTop, CosineMixtureTransfer.weightedEnergyENN
      Legacy.BecknerOnofri.GaussianLattice.spectralWeight (CosineMixture.mixture (range m) w N) ≤
      ENNReal.ofReal ((2 * A - 3 / (1100 * (d : ℝ)) * γ) /
        (2 * Legacy.BecknerOnofri.endpointConstant d)) := by
    filter_upwards [hγ] with m hmγ
    rw [CosineMixtureTransfer.finite_weightedEnergyENN (range m) w N _ hsw]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hc]
    have := hpart m
    nlinarith [mul_le_mul_of_nonneg_left hmγ hg.le]
  have hbound := weightedEnergyENN_le_of_eventually w N hw hs _ _ hC
  have hspec : spectralEnergy ρ = CosineMixtureTransfer.weightedEnergyENN
      Legacy.BecknerOnofri.GaussianLattice.spectralWeight (CosineMixtureApproximation.rho w N) :=
    (spectralEnergy_eq_weightedEnergyENN hd0 ρ).trans (weightedEnergyENN_congr_ae' _ he)
  rw [← hspec] at hbound
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound, ?_⟩
  have hreal := ENNReal.toReal_le_of_le_ofReal hBnn hbound
  rw [le_div_iff₀ hc] at hreal
  linarith [hA]

end BecknerOnofri.V2.Section3
