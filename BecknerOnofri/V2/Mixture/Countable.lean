module

public import BecknerOnofri.V2.Mixture.Finite
public import BecknerOnofri.CountableMixtureTransfer
public import BecknerOnofri.ContinuousMixtureMajorant

@[expose] public section

/-! # Proposition 5.11 (`prop:section5-singular-fourier-tail`): countable correlated mixtures and
smooth densities

The finite estimate of `Finite.lean` is passed to the limit `m → ∞` along the partial mixtures
`∑_{n<m} w_n ∏_i h_{N_n,i}` of a countable mixture with arbitrary (correlated) summable weights.
The convergence statements (`partial_weighted_energy_tendsto`, `rho_fourier`,
`summable_mixture_coeff`, `summable_fourier_sq`) are the generic v1 transfer lemmas of
`CountableMixtureTransfer`; the `j ≥ 4` axis tail convergence is re-proved here (dominated
convergence, `tendsto_tsum_of_dominated_convergence`).  The final theorem for a smooth
probability density `IsCountableCosineMixture ρ` is exactly the statement of Proposition 5.11, with
the coefficients `1/40, 2/15, 27/40`.  The v1 budget-hardwired
`countable_mixture_tail_of_scalar` / `smooth_mixture_singular_tail` are not used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Filter
open scoped Topology
namespace BecknerOnofri.V2.Mixture

open BecknerOnofri.V2.ThetaTail (cube12 latticeNorm)
open BecknerOnofri.HighDim.EntropyTail (scalarTailWeight scalarTailWeight_nonneg
  scalarTailWeight_le_one)
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open BecknerOnofri.CosineMixtureTransfer

theorem axis_tail_injective (i : Fin 12) :
    Function.Injective (fun j : ℕ => (Pi.single i ((j : ℤ) + 4) : Fin 12 → ℤ)) := by
  intro a b h
  have hh := congrFun h i
  simp only [Pi.single_eq_same] at hh
  omega

theorem partial_fourier_sq_tendsto (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (k : Fin 12 → ℤ) :
    Tendsto (fun m : ℕ => ‖densityFourier (CosineMixture.mixture (range m) w N) k‖ ^ 2) atTop
      (𝓝 (‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2)) := by
  simp_rw [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact ((summable_mixture_coeff w N hw hs k).hasSum.tendsto_sum_nat).pow 2

theorem partial_fourier_sq_le (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w) (m : ℕ) (k : Fin 12 → ℤ) :
    ‖densityFourier (CosineMixture.mixture (range m) w N) k‖ ^ 2 ≤
      ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2 := by
  have hnon : 0 ≤ ∑ n ∈ range m, w n * RandomRectangles.componentCoeff (N n) k :=
    sum_nonneg (fun n _ => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  have hle := (summable_mixture_coeff w N hw hs k).sum_le_tsum (range m)
    (fun n _ => mul_nonneg (hw n) (RandomRectangles.componentCoeff_nonneg _ _))
  simp only [CosineMixture.mixture_fourier, rho_fourier w N hw hs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (sq_le_sq₀ hnon (hnon.trans hle)).mpr hle

theorem partial_axis_tail_tendsto (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) (i : Fin 12) :
    Tendsto (fun m : ℕ => ∑' j : ℕ,
      ‖densityFourier (CosineMixture.mixture (range m) w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
        ((j : ℝ) + 4)) atTop
      (𝓝 (∑' j : ℕ,
        ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
          ((j : ℝ) + 4))) := by
  have hdom := (summable_fourier_sq
    (CosineMixtureApproximation.rho_continuous w N hw hSup)).comp_injective
    (axis_tail_injective i)
  apply tendsto_tsum_of_dominated_convergence hdom
  · intro j
    exact (partial_fourier_sq_tendsto w N hw hs _).div_const _
  · apply Eventually.of_forall
    intro m j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hj : (1 : ℝ) ≤ (j : ℝ) + 4 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    exact (div_le_self (sq_nonneg _) hj).trans
      (partial_fourier_sq_le w N hw hs m _)

/-- **Proposition 5.11 for countable mixtures with arbitrary correlated weights**
(`w ≥ 0` summable, with the summable majorant at the origin).  The coefficients are
`1/40, 2/15, 27/40`. -/
theorem countable_mixture_singular_tail
    (w : ℕ → ℝ) (N : ℕ → Fin 12 → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0)) :
    (1 / 2 : ℝ) * ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
        (fun k => (latticeNorm k ^ 12)⁻¹ *
          ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2) k ≤
      ∑ i : Fin 12,
        (1 / 40 * ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (2 : ℤ))‖ ^ 2 +
          2 / 15 * ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i (3 : ℤ))‖ ^ 2 +
          27 / 40 * ∑' j : ℕ,
            ‖densityFourier (CosineMixtureApproximation.rho w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
              ((j : ℝ) + 4)) := by
  have hl := (partial_weighted_energy_tendsto w N hw hs hSup scalarTailWeight
    (fun k => ⟨scalarTailWeight_nonneg k, scalarTailWeight_le_one k⟩)).const_mul (1 / 2 : ℝ)
  have hr := tendsto_finsetSum univ (fun i _ =>
    ((((partial_fourier_sq_tendsto w N hw hs (Pi.single i (2 : ℤ))).const_mul (1 / 40 : ℝ)).add
      ((partial_fourier_sq_tendsto w N hw hs (Pi.single i (3 : ℤ))).const_mul (2 / 15 : ℝ))).add
      ((partial_axis_tail_tendsto w N hw hs hSup i).const_mul (27 / 40 : ℝ))))
  have key := le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun m => by
    have h := finite_mixture_singular_tail (range m) w N (fun n _ => hw n)
    simp_rw [tailWeight_mul_eq_indicator]
    exact h)
  simp_rw [tailWeight_mul_eq_indicator] at key
  exact key

/-- **Proposition 5.11** (`prop:section5-singular-fourier-tail`, `eq:section5-global-tail-energy`):
every smooth probability density of the form `eq:mixture` on `𝕋¹²` satisfies
`½ ∑_{k∉{-1,0,1}¹²} |k|⁻¹² |ρ̂(k)|² ≤ ∑_{i=1}^{12} [ 1/40 |ρ̂(2e_i)|² + 2/15 |ρ̂(3e_i)|²
+ 27/40 ∑_{n≥4} |ρ̂(n e_i)|²/n ]`.
The mixture weights may be arbitrarily correlated.  No scalar hypothesis is assumed: the scalar
bound `T_n ≤ R_n` is `ThetaTail.RouteM.Tn_le_Rn`. -/
theorem singular_fourier_tail (ρ : HighDim.ProbabilityDensity 12)
    (hs : HighDim.SmoothOnTorus ρ.value) (hρ : HighDim.IsCountableCosineMixture ρ) :
    (1 / 2 : ℝ) * ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
        (fun k => (latticeNorm k ^ 12)⁻¹ * ‖HighDim.fourierCoeff ρ.value k‖ ^ 2) k ≤
      ∑ i : Fin 12,
        (1 / 40 * ‖HighDim.fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖ ^ 2 +
          2 / 15 * ‖HighDim.fourierCoeff ρ.value (Pi.single i (3 : ℤ))‖ ^ 2 +
          27 / 40 * ∑' j : ℕ,
            ‖HighDim.fourierCoeff ρ.value (Pi.single i ((j : ℤ) + 4))‖ ^ 2 / ((j : ℝ) + 4)) := by
  obtain ⟨w, N, hw, hm, he⟩ := hρ
  have he' : ρ.value =ᵐ[HighDim.torusMeasure 12]
      Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N := he
  have hSup := CosineMixtureTransfer.mixture_majorant_of_continuous ρ.value
    (HighDim.UniformFourier.smooth_continuous hs) w N hw hm.summable he'
  have htail := countable_mixture_singular_tail w N hw hm.summable hSup
  have hf (k : Fin 12 → ℤ) : HighDim.fourierCoeff ρ.value k =
      HighDim.fourierCoeff (Legacy.BecknerOnofri.CosineMixtureApproximation.rho w N) k := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [he'] with x hx
    rw [hx]
  simp_rw [hf]
  exact htail

end BecknerOnofri.V2.Mixture
