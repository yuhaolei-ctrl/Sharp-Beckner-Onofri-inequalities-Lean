import BecknerOnofri.MixtureComparisonGe12

/-! Extended nonnegative energies of arbitrary countable cosine mixtures.
No uniform spatial majorant is assumed in the approximation lemmas. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open Finset MeasureTheory Filter
namespace BecknerOnofri.CosineMixtureTransfer
open RectangleLattice RandomRectangles Legacy.TorusEndpoint
open Legacy.BecknerOnofri Legacy.D10

/-- Nonnegative weighted Fourier energy, allowing divergence. -/
def weightedEnergyENN {d : ℕ} (g : Frequency d → ℝ) (f : Torus d → ℝ) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (g k*‖densityFourier f k‖^2)

lemma finite_weightedEnergyENN {α : Type*} {d : ℕ} (s : Finset α) (w : α → ℝ)
    (N : α → Fin d → ℕ) (g : Frequency d → ℝ) (hg : ∀ k, 0 ≤ g k) :
    weightedEnergyENN g (CosineMixture.mixture s w N) =
      ENNReal.ofReal (∑' k, g k*‖densityFourier (CosineMixture.mixture s w N) k‖^2) := by
  have hs : Summable (fun k => g k*‖densityFourier (CosineMixture.mixture s w N) k‖^2) := by
    simp_rw [weighted_mixture_eq_latent]
    exact summable_latentTerm s w N g
  exact (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hg k) (sq_nonneg _)) hs).symm

lemma partial_weightedEnergyENN_le {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (g : Frequency d → ℝ) (hg : ∀ k, 0 ≤ g k)
    (m : ℕ) : weightedEnergyENN g (CosineMixture.mixture (range m) w N) ≤
      weightedEnergyENN g (CosineMixtureApproximation.rho w N) := by
  apply ENNReal.tsum_le_tsum
  intro k
  apply ENNReal.ofReal_le_ofReal
  simp only [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hp : 0 ≤ ∑ n ∈ range m, w n*componentCoeff (N n) k :=
    sum_nonneg (fun n _ => mul_nonneg (hw n) (componentCoeff_nonneg _ _))
  have hle := (summable_mixture_coeff w N hw hs k).sum_le_tsum (range m)
    (fun n _ => mul_nonneg (hw n) (componentCoeff_nonneg _ _))
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hp (hp.trans hle)).mpr hle) (hg k)

/-- Finite-frequency limits and positivity suffice for passing an energy bound;
no Parseval bound or pointwise boundedness of the full mixture is needed. -/
lemma weightedEnergyENN_le_of_partial_bounds {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (g : Frequency d → ℝ) (C : ℝ≥0∞)
    (hb : ∀ m, weightedEnergyENN g (CosineMixture.mixture (range m) w N) ≤ C) :
    weightedEnergyENN g (CosineMixtureApproximation.rho w N) ≤ C := by
  unfold weightedEnergyENN
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  have hpoint (k : Frequency d) : Tendsto (fun m =>
      ENNReal.ofReal (g k*‖densityFourier (CosineMixture.mixture (range m) w N) k‖^2)) atTop
      (𝓝 (ENNReal.ofReal (g k*‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2))) := by
    simp only [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hc := (summable_mixture_coeff w N hw hs k).hasSum.tendsto_sum_nat
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hc.pow 2).const_mul (g k))
  apply le_of_tendsto (tendsto_finsetSum S (fun k _ => hpoint k))
  exact Eventually.of_forall (fun m => (ENNReal.sum_le_tsum S).trans (hb m))

#print axioms finite_weightedEnergyENN
#print axioms partial_weightedEnergyENN_le
#print axioms weightedEnergyENN_le_of_partial_bounds
end BecknerOnofri.CosineMixtureTransfer
