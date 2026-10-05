import BecknerOnofri.FiniteEntropyEnergy
import Mathlib.Analysis.Normed.Group.Tannery

/-! Convergence of actual heat-regularized spectral energy for finite entropy. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim
open Legacy.TorusEndpoint Legacy.BecknerOnofri

theorem heat_spectralTerm_le {d : ℕ} (ρ : Legacy.TorusEndpoint.ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) (k : Legacy.TorusEndpoint.NonzeroFrequency d) :
    densitySpectralTerm (HeatDensityApproximation.heatDensity ρ ht) k ≤
      densitySpectralTerm ρ k := by
  unfold densitySpectralTerm
  change ‖densityFourier (HeatDensityApproximation.heatValue ρ t) k.val‖ ^ 2 / _ ≤ _
  rw [HeatDensityApproximation.heatValue_fourier ρ ht, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (TorusHeatBounds.heatWeight_pos t k.val)]
  apply div_le_div_of_nonneg_right _ (pow_nonneg (Real.sqrt_nonneg _) _)
  apply pow_le_pow_left₀ (mul_nonneg (TorusHeatBounds.heatWeight_pos t k.val).le (norm_nonneg _))
  exact mul_le_of_le_one_left (norm_nonneg _)
    (GreenHeatRegularization.heatWeight_le_one ht.le k.val)

theorem heat_fourierEnergy_tendsto {d : ℕ} (hd : 0 < d)
    (ρ : Legacy.TorusEndpoint.ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => fourierEnergy (HeatDensityApproximation.heatDensity ρ (ht n)))
      atTop (𝓝 (fourierEnergy ρ)) := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hs := (legacy_rough_finite_entropy hd ρ hρ
    (by positivity : 0 < endpointConstant d / 2) (by linarith)).1
  unfold fourierEnergy
  apply tendsto_tsum_of_dominated_convergence hs
  · intro k
    exact ((HeatDensityApproximation.heatDensity_fourier_tendsto ρ t ht ht0 k.val).norm.pow 2).div_const _
  · exact Eventually.of_forall (fun n k => by
      have hn : 0 ≤ densitySpectralTerm (HeatDensityApproximation.heatDensity ρ (ht n)) k :=
        div_nonneg (sq_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      exact heat_spectralTerm_le ρ (ht n) k)

#print axioms heat_fourierEnergy_tendsto
end BecknerOnofri.HighDim
