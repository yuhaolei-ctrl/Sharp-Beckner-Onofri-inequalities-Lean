module

public import BecknerOnofri.CountableMixtureExtendedMarginals
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section

/-! Countable probability mixtures converge in L1 without a uniform majorant. -/
noncomputable section
open scoped BigOperators Topology ENNReal
open Finset MeasureTheory Filter
namespace BecknerOnofri.CosineMixtureTransfer
open Legacy.TorusEndpoint Legacy.BecknerOnofri

lemma rho_summable_ae {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    ∀ᵐ x ∂torusMeasure d, Summable (fun n => w n * CosineMixture.tensor (N n) x) := by
  have hi (n : ℕ) := (CosineMixture.tensor_integrable (N n)).const_mul (w n)
  have he (n : ℕ) : eLpNorm (fun x => w n * CosineMixture.tensor (N n) x) 1
      (torusMeasure d) = ENNReal.ofReal (w n) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    congr 1
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))]
    rw [integral_const_mul, CosineMixture.tensor_mass, mul_one]
  have hb : (∑' n, eLpNorm (fun x => w n * CosineMixture.tensor (N n) x) 1
      (torusMeasure d)) ≠ ⊤ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg hw hs]
    exact ENNReal.ofReal_ne_top
  have h := summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl hb
  exact h.mono (fun x hx => hx.of_norm)

lemma mixture_partial_l1_exact {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) (m : ℕ) :
    (∫ x, ‖CosineMixtureApproximation.rho w N x - CosineMixture.mixture (range m) w N x‖
      ∂torusMeasure d) = 1 - ∑ n ∈ range m, w n := by
  have hle : CosineMixture.mixture (range m) w N ≤ᵐ[torusMeasure d]
      CosineMixtureApproximation.rho w N := by
    filter_upwards [rho_summable_ae w N hw hm.summable] with x hx
    exact hx.sum_le_tsum (range m) (fun n _ => mul_nonneg (hw n) (CosineMixture.tensor_nonneg _ _))
  rw [integral_congr_ae (hle.mono (fun x hx => Real.norm_of_nonneg (sub_nonneg.mpr hx)))]
  rw [integral_sub (rho_integrable_mass_one w N hw hm) (CosineMixture.mixture_integrable _ _ _),
    CosineMixtureApproximation.rho_mass w N hw hm, CosineMixture.mixture_mass]

theorem mixture_partial_l1_tendsto {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) :
    Tendsto (fun m => ∫ x,
      ‖CosineMixtureApproximation.rho w N x - CosineMixture.mixture (range m) w N x‖
      ∂torusMeasure d) atTop (𝓝 0) := by
  simp_rw [mixture_partial_l1_exact w N hw hm]
  simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hm.tendsto_sum_nat

#print axioms rho_summable_ae
#print axioms mixture_partial_l1_exact
#print axioms mixture_partial_l1_tendsto
end BecknerOnofri.CosineMixtureTransfer
