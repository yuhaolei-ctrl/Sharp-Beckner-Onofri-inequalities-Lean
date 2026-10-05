import BecknerOnofri.EntropyTailMixtureBudget
import BecknerOnofri.CountableMixtureTransfer

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter
namespace BecknerOnofri.HighDim.EntropyTail
open Legacy.TorusEndpoint Legacy.BecknerOnofri Finset
open CosineMixtureTransfer

theorem partial_fourier_sq_tendsto (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Frequency 12) :
    Tendsto (fun m : ℕ => ‖densityFourier (CosineMixture.mixture (range m) w N) k‖^2) atTop
      (𝓝 (‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2)) := by
  simp_rw [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact ((summable_mixture_coeff w N hw hs k).hasSum.tendsto_sum_nat).pow 2

theorem partial_fourier_sq_le (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (m : ℕ) (k : Frequency 12) :
    ‖densityFourier (CosineMixture.mixture (range m) w N) k‖^2 ≤
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2 := by
  have hnon : 0 ≤ ∑ n ∈ range m, w n*RandomRectangles.componentCoeff (N n) k :=
    sum_nonneg (fun n _ => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  have hle := (summable_mixture_coeff w N hw hs k).sum_le_tsum (range m)
    (fun n _ => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  simp only [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (sq_le_sq₀ hnon (hnon.trans hle)).mpr hle

theorem axis_tail_injective (i : Fin 12) :
    Function.Injective (fun j : ℕ => (Pi.single i (j+3 : ℤ) : Frequency 12)) := by
  intro a b h
  have hh := congrFun h i
  simp only [Pi.single_eq_same] at hh
  omega

theorem partial_axis_tail_tendsto (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n*CosineMixture.tensor (N n) 0)) (i : Fin 12) :
    Tendsto (fun m : ℕ => ∑' j : ℕ,
      ‖densityFourier (CosineMixture.mixture (range m) w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ))
      atTop (𝓝 (∑' j : ℕ,
        ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ))) := by
  have hdom := (summable_fourier_sq (CosineMixtureApproximation.rho_continuous w N hw hSup)).comp_injective
    (axis_tail_injective i)
  apply tendsto_tsum_of_dominated_convergence hdom
  · intro j
    exact (partial_fourier_sq_tendsto w N hw hs _).div_const _
  · apply Eventually.of_forall
    intro m j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hj : (1 : ℝ) ≤ (j : ℝ)+3 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    exact (div_le_self (sq_nonneg _) hj).trans
      (partial_fourier_sq_le w N hw hs m _)

/-- Countable, correlated mixture transfer along the manuscript's scalar tail route. -/
theorem countable_mixture_tail_of_scalar
    (hscalar : ∀ n : ℕ, scalarTail n ≤ scalarBudget n)
    (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n*CosineMixture.tensor (N n) 0)) :
    (1/2 : ℝ)*(∑' k : Frequency 12,
      scalarTailWeight k*‖densityFourier (CosineMixtureApproximation.rho w N) k‖^2) ≤
      ∑ i : Fin 12, ((21/1000)*‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (2 : ℤ))‖^2+
        (27/40)*∑' j : ℕ, ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (j+3 : ℤ))‖^2/(j+3 : ℝ)) := by
  have hl := (partial_weighted_energy_tendsto w N hw hs hSup scalarTailWeight
    (fun k => ⟨scalarTailWeight_nonneg k, scalarTailWeight_le_one k⟩)).const_mul (1/2 : ℝ)
  have hr := tendsto_finsetSum univ (fun i _ =>
    ((partial_fourier_sq_tendsto w N hw hs (Pi.single i (2 : ℤ))).const_mul (21/1000 : ℝ)).add
      ((partial_axis_tail_tendsto w N hw hs hSup i).const_mul (27/40 : ℝ)))
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun m =>
    finite_mixture_tail_of_scalar hscalar (range m) w N (fun n _ => hw n))

#print axioms countable_mixture_tail_of_scalar
end BecknerOnofri.HighDim.EntropyTail
