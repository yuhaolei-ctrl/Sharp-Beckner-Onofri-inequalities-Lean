module

public import BecknerOnofri.V2.Mixture.Scalar

@[expose] public section

/-! # Proposition 5.11 for finite correlated mixtures (Subsubsection `subsec:section5-global-tail`)

For a finite mixture `ρ = ∑_a w_a ∏_i h_{N_a,i}` with arbitrary (possibly correlated) nonnegative
weights, the pair `(N, M)` of independent index vectors and the coordinatewise hypergeometric
latent draw `L` of the proof are encoded by the v1 *generic* finite average `latentAverage`
(weights `w_a w_b` and hypergeometric product law `latentWeight (N a) (N b) L` on `latentBox (N a)`).
The hypergeometric identity `|ρ̂(k)|² = E ∏_i a_{L_i}(k_i)` is the v1 theorem
`CosineMixtureTransfer.weighted_mixture_eq_latent`; in particular `latentAverage_axis` is
`E[a_{L_i}(j)] = |ρ̂(j e_i)|²`.  Fubini--Tonelli for the finite sum is `Finset.sum_comm` /
`Summable.tsum_finsetSum` (`latentAverage_tsum`, re-proved here for the `j ≥ 4` tail).

Only the scalar input `Tn_le_Rn` (unconditional, `RouteM`) is used; none of the v1
budget-hardwired theorems is imported. -/
noncomputable section
open Finset
namespace BecknerOnofri.V2.Mixture

open BecknerOnofri.V2.ThetaTail (aCoef Hn Tn Rn cube12 latticeNorm)
open BecknerOnofri.HighDim.EntropyTail (scalarCoefficient scalarTail scalarTailWeight
  scalarHarmonic_summable latentAverage latentAverage_mono latentAverage_add latentAverage_mul
  latentAverage_sum latentAverage_axis finite_mixture_tail_comparison)
open Legacy.TorusEndpoint Legacy.BecknerOnofri

/-- `R_n` in the v1 notation (`eq:section5-global-harmonic-tail`). -/
theorem Rn_eq_scalar (n : ℕ) :
    Rn n = 3 / 5 * scalarCoefficient n 2 + 16 / 5 * scalarCoefficient n 3 +
      81 / 5 * ∑' j : ℕ, scalarCoefficient n (j + 4) / ((j : ℝ) + 4) := by
  rw [Rn_eq_positive]
  have h2 : scalarCoefficient n 2 = aCoef n 2 := by
    simpa using scalarCoefficient_eq_aCoef n 2
  have h3 : scalarCoefficient n 3 = aCoef n 3 := by
    simpa using scalarCoefficient_eq_aCoef n 3
  rw [h2, h3]
  congr 3

/-- Exchange of the (nonnegative-term) `j`-sum with the finite latent average
(Fubini--Tonelli for a finite sum). Generic; re-proved here, without the budget module. -/
theorem latentAverage_tsum {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (F : ℕ → (Fin 12 → ℕ) → ℝ) (hF : ∀ L, Summable (fun j => F j L)) :
    (∑' j, latentAverage s w N (F j)) = latentAverage s w N (fun L => ∑' j, F j L) := by
  unfold latentAverage
  rw [Summable.tsum_finsetSum]
  · apply sum_congr rfl
    intro a _
    rw [Summable.tsum_finsetSum]
    · apply sum_congr rfl
      intro b _
      rw [Summable.tsum_finsetSum]
      · simp_rw [tsum_mul_left]
      · intro L _
        exact (hF L).mul_left _
    · intro b _
      exact summable_sum (fun L _ => (hF L).mul_left _)
  · intro a _
    exact summable_sum (fun b _ => summable_sum (fun L _ => (hF L).mul_left _))

/-- `E[∑_{j≥4} a_{L_i}(j)/j] = ∑_{j≥4} |ρ̂(j e_i)|²/j`. -/
theorem latentAverage_axis_tail {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ)
    (i : Fin 12) :
    latentAverage s w N (fun L => ∑' j : ℕ, scalarCoefficient (L i) (j + 4) / ((j : ℝ) + 4)) =
      ∑' j : ℕ, ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
        ((j : ℝ) + 4) := by
  have hs (L : Fin 12 → ℕ) :
      Summable (fun j : ℕ => scalarCoefficient (L i) (j + 4) / ((j : ℝ) + 4)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using
      (scalarHarmonic_summable (L i)).comp_injective
        (show Function.Injective (fun j : ℕ => j + 4) from fun a b h => by dsimp at h; omega)
  rw [← latentAverage_tsum s w N _ hs]
  apply tsum_congr
  intro j
  simp_rw [div_eq_mul_inv, mul_comm _ (((j : ℝ) + 4)⁻¹)]
  rw [latentAverage_mul, latentAverage_axis]
  norm_num only [Nat.cast_add, Nat.cast_ofNat]

/-- The latent average of `(1/12) ∑_i R_{L_i}` is the positive-coefficient sum of the manuscript's
last display `eq:section5-global-tail-mixture-calculation`. -/
theorem latentAverage_Rn {α : Type*} (s : Finset α) (w : α → ℝ) (N : α → Fin 12 → ℕ) :
    latentAverage s w N (fun L => (1 / 12 : ℝ) * ∑ i : Fin 12, Rn (L i)) =
      (1 / 12 : ℝ) * ∑ i : Fin 12,
        (3 / 5 * ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (2 : ℤ))‖ ^ 2 +
          16 / 5 * ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (3 : ℤ))‖ ^ 2 +
          81 / 5 * ∑' j : ℕ,
            ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
              ((j : ℝ) + 4)) := by
  simp_rw [Rn_eq_scalar]
  rw [latentAverage_mul, latentAverage_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [latentAverage_add, latentAverage_add, latentAverage_mul, latentAverage_mul,
    latentAverage_mul, latentAverage_axis, latentAverage_axis, latentAverage_axis_tail]
  norm_num only [Nat.cast_ofNat]

/-- The tail weight times a square, as the indicator of the complement of the cube. -/
theorem tailWeight_mul_eq_indicator (k : Fin 12 → ℤ) (x : ℝ) :
    scalarTailWeight k * x = (cube12ᶜ).indicator (fun k => (latticeNorm k ^ 12)⁻¹ * x) k := by
  rw [scalarTailWeight_eq_indicator]
  by_cases hk : k ∈ cube12ᶜ
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
  · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]

/-- **Proposition 5.11 for finite mixtures with arbitrary (correlated) nonnegative weights**,
with the coefficients `1/40, 2/15, 27/40` of `eq:section5-global-tail-energy`.
Fubini--Tonelli (`latentAverage_*`), `eq:section5-global-tail-arbitrary-indices`
(`tail_arbitrary_indices`, through `finite_mixture_tail_comparison`) and the scalar bound
`Lemma section5-global-scalar-tail` (`RouteM.Tn_le_Rn`) are used. -/
theorem finite_mixture_singular_tail {α : Type*} (s : Finset α) (w : α → ℝ)
    (N : α → Fin 12 → ℕ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    (1 / 2 : ℝ) * ∑' k : Fin 12 → ℤ, (cube12ᶜ).indicator
        (fun k => (latticeNorm k ^ 12)⁻¹ *
          ‖densityFourier (CosineMixture.mixture s w N) k‖ ^ 2) k ≤
      ∑ i : Fin 12,
        (1 / 40 * ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (2 : ℤ))‖ ^ 2 +
          2 / 15 * ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i (3 : ℤ))‖ ^ 2 +
          27 / 40 * ∑' j : ℕ,
            ‖densityFourier (CosineMixture.mixture s w N) (Pi.single i ((j : ℤ) + 4))‖ ^ 2 /
              ((j : ℝ) + 4)) := by
  have h1 := finite_mixture_tail_comparison s w N hw
  simp_rw [tailWeight_mul_eq_indicator] at h1
  have h2 : latentAverage s w N (fun L => (1 / 12 : ℝ) * ∑ i : Fin 12, scalarTail (L i)) ≤
      latentAverage s w N (fun L => (1 / 12 : ℝ) * ∑ i : Fin 12, Rn (L i)) := by
    apply latentAverage_mono s w N hw
    intro L
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply sum_le_sum
    intro i _
    rw [scalarTail_eq_Tn]
    exact ThetaTail.RouteM.Tn_le_Rn _
  have h3 := (h1.trans h2).trans_eq (latentAverage_Rn s w N)
  have h4 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine h4.trans_eq ?_
  rw [← mul_assoc, show (1 / 2 : ℝ) * (1 / 12) = 1 / 24 by norm_num, one_div, one_div,
    mul_sum]
  apply sum_congr rfl
  intro i _
  ring

end BecknerOnofri.V2.Mixture
