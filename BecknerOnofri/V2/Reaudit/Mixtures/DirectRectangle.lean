module

public import BecknerOnofri.V2.Reaudit.Mixtures.Radii
public import BecknerOnofri.MixtureComparisonGe12
public import BecknerOnofri.CountableMixtureExtendedComparison

@[expose] public section

/-! # `prop:spectral-marginal-energy`, the direct random-rectangle argument (S037)

For a countable cosine-power mixture `ρ = ∑_a w_a ⊗_i h_{N_a,i}` the proof printed in the manuscript
is, in this file:

1. `|ρ̂(k)|² = ∑_{(a,b)} w_a w_b ∏_i a_{N_a,i}(k_i) a_{N_b,i}(k_i)` (Tonelli on `ℕ × ℕ`; `energy_term_eq_pairs`);
2. for each pair the product of survival functions is the probability that independent radii with
   `P(R_i = m) = a a - a a` contain `k` (`Radii.rect_survival`), hence for every nonnegative weight `g`
   `∑_k g(k) ∏_i a a = E_R ∑_{k ∈ box R} g(k)` (`pair_tsum`);
3. Tonelli on the nonnegative energy sums turns both sides of `eq:spectral-energy-main` into
   `∑_{(a,b)} w_a w_b E_R [S_d(R)]` and `∑_{(a,b)} w_a w_b E_R [S_{d-1}(R_{-i})]`
   (`weightedEnergyENN_eq_pairs`);
4. Lemma 5.4 (`RectangleLattice.rectangle_comparison_ge12`), applied inside the expectation, and
   Tonelli again (`weightedEnergyENN_deletion_direct`).

No hypergeometric latent index, no finite truncation of the mixture, no majorant. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace BecknerOnofri.V2.Reaudit.Mixtures
open BecknerOnofri.RectangleLattice BecknerOnofri.RandomRectangles Legacy.D10
open BecknerOnofri.CosineMixtureTransfer Legacy.TorusEndpoint Legacy.BecknerOnofri

variable {d : ℕ}

/-- The expected value, over independent radii for the pair `(N_a, N_b)`, of the box sum of `g`. -/
def pairRect (N : ℕ → Fin d → ℕ) (g : Frequency d → ℝ) (a b : ℕ) : ℝ :=
  ∑ R ∈ latentBox (N a), rectLaw (pairSurvival (N a) (N b)) R * ∑ k ∈ box R, g k

theorem pairRect_nonneg (N : ℕ → Fin d → ℕ) {g : Frequency d → ℝ} (hg : ∀ k, 0 ≤ g k) (a b : ℕ) :
    0 ≤ pairRect N g a b :=
  sum_nonneg fun R _ => mul_nonneg (rectLaw_nonneg (pairSurvival_antitone _ _) R)
    (sum_nonneg fun k _ => hg k)

/-- For one pair `(a, b)` the (extended) Fourier energy contribution is the expected box sum. -/
theorem pair_tsum (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    {g : Frequency d → ℝ} (hg : ∀ k, 0 ≤ g k) (a b : ℕ) :
    (∑' k, ENNReal.ofReal (g k * ((w a * componentCoeff (N a) k) *
        (w b * componentCoeff (N b) k)))) =
      ENNReal.ofReal (w a * w b * pairRect N g a b) := by
  have hfin : ∀ k ∉ box (N a), ENNReal.ofReal (g k * ((w a * componentCoeff (N a) k) *
      (w b * componentCoeff (N b) k))) = 0 := by
    intro k hk
    rw [componentCoeff_eq_zero hk]
    simp
  rw [tsum_eq_sum hfin, ← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    unfold pairRect
    have h1 : ∀ k ∈ box (N a), g k * ((w a * componentCoeff (N a) k) *
        (w b * componentCoeff (N b) k)) =
        w a * w b * (g k * ∏ i, pairSurvival (N a) (N b) i (k i).natAbs) := by
      intro k _
      rw [← componentCoeff_mul]
      ring
    rw [sum_congr rfl h1, ← mul_sum,
      sum_rect (pairSurvival (N a) (N b)) (N a) (fun i j hj => pairSurvival_zero _ _ i j hj) g]
  · intro k _
    exact mul_nonneg (hg k) (mul_nonneg (mul_nonneg (hw a) (componentCoeff_nonneg _ _))
      (mul_nonneg (hw b) (componentCoeff_nonneg _ _)))

/-- Tonelli: `|ρ̂(k)|²` as a double sum over the independent pair `(N, M)`. -/
theorem energy_term_eq_pairs (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) {g : Frequency d → ℝ} (hg : ∀ k, 0 ≤ g k) (k : Frequency d) :
    ENNReal.ofReal (g k * ‖densityFourier (CosineMixtureApproximation.rho w N) k‖ ^ 2) =
      ∑' a, ∑' b, ENNReal.ofReal (g k * ((w a * componentCoeff (N a) k) *
        (w b * componentCoeff (N b) k))) := by
  have hx : ∀ a, 0 ≤ w a * componentCoeff (N a) k := fun a =>
    mul_nonneg (hw a) (componentCoeff_nonneg _ _)
  have hsum := summable_mixture_coeff w N hw hs k
  rw [rho_fourier w N hw hs, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq,
    ENNReal.ofReal_mul (hg k), ENNReal.ofReal_mul (tsum_nonneg hx),
    ENNReal.ofReal_tsum_of_nonneg hx hsum]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  congr 1
  funext a
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  congr 1
  funext b
  rw [ENNReal.ofReal_mul (hg k), ENNReal.ofReal_mul (hx a)]

/-- Both sides of `eq:spectral-box-expectations`: the energy of `ρ` for a nonnegative weight `g`
is the `(a, b)`-sum of the expected box sums of `g`. -/
theorem weightedEnergyENN_eq_pairs (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) {g : Frequency d → ℝ} (hg : ∀ k, 0 ≤ g k) :
    weightedEnergyENN g (CosineMixtureApproximation.rho w N) =
      ∑' a, ∑' b, ENNReal.ofReal (w a * w b * pairRect N g a b) := by
  unfold weightedEnergyENN
  simp_rw [energy_term_eq_pairs w N hw hs hg]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun a => ?_)
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun b => ?_)
  exact pair_tsum w N hw hg a b

/-- Lemma 5.4 inside the expectation over the radii. -/
theorem pairRect_comparison (hd : 12 ≤ d) (N : ℕ → Fin d → ℕ) (a b : ℕ) :
    pairRect N (weight (d : ℝ)) a b ≤ (1 / ((d : ℝ) - 1)) *
      ∑ i : Fin d, pairRect N (fun k => if k i = 0 then weight ((d : ℝ) - 1) k else 0) a b := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdm : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (12 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold pairRect
  simp_rw [← latticeSum_eq_sum_box hdpos]
  have hmask : ∀ (i : Fin d) (R : Fin d → ℕ),
      (∑ k ∈ box R, if k i = 0 then weight ((d : ℝ) - 1) k else 0) =
        latticeSum ((d : ℝ) - 1) (Function.update R i 0) := by
    intro i R
    rw [latticeSum_eq_sum_box hdm, box_delete, sum_filter]
  simp_rw [hmask]
  rw [sum_comm (s := univ), mul_sum]
  apply sum_le_sum
  intro R _
  calc rectLaw (pairSurvival (N a) (N b)) R * latticeSum (d : ℝ) R
      ≤ rectLaw (pairSurvival (N a) (N b)) R * ((1 / ((d : ℝ) - 1)) *
          ∑ i : Fin d, latticeSum ((d : ℝ) - 1) (Function.update R i 0)) :=
        mul_le_mul_of_nonneg_left (rectangle_comparison_ge12 hd R)
          (rectLaw_nonneg (pairSurvival_antitone _ _) R)
    _ = _ := by rw [← mul_sum]; ring

/-- **`eq:spectral-energy-main` for the energy sums**, by the direct random-rectangle argument:
the same statement as `CosineMixtureTransfer.countable_mixture_comparison_enn`. -/
theorem countable_mixture_comparison_enn_direct (hd : 12 ≤ d)
    (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n) (hs : Summable w) :
    weightedEnergyENN (weight (d:ℝ)) (CosineMixtureApproximation.rho w N) ≤
      ENNReal.ofReal (1 / ((d:ℝ)-1)) * ∑ i : Fin d,
        weightedEnergyENN (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0)
          (CosineMixtureApproximation.rho w N) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdm : (0:ℝ) < (d:ℝ)-1 := by
    have : (12:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hg0 : ∀ k : Frequency d, 0 ≤ weight (d:ℝ) k := fun k => weight_nonneg _ _
  have hgi : ∀ (i : Fin d) (k : Frequency d), 0 ≤ (if k i = 0 then weight ((d:ℝ)-1) k else 0) := by
    intro i k
    split_ifs
    · exact weight_nonneg _ _
    · exact le_rfl
  rw [weightedEnergyENN_eq_pairs w N hw hs hg0]
  simp_rw [weightedEnergyENN_eq_pairs w N hw hs (hgi _)]
  have hc : 0 ≤ 1 / ((d:ℝ)-1) := div_nonneg (by norm_num) hdm.le
  calc ∑' a, ∑' b, ENNReal.ofReal (w a * w b * pairRect N (weight (d:ℝ)) a b)
      ≤ ∑' a, ∑' b, ENNReal.ofReal (1 / ((d:ℝ)-1)) * ∑ i : Fin d, ENNReal.ofReal
          (w a * w b * pairRect N (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0) a b) := by
        refine ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b => ?_))
        have hwab : 0 ≤ w a * w b := mul_nonneg (hw a) (hw b)
        have h1 := mul_le_mul_of_nonneg_left (pairRect_comparison hd N a b) hwab
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hwab
            (pairRect_nonneg N (hgi i) a b)), ← ENNReal.ofReal_mul hc]
        apply ENNReal.ofReal_le_ofReal
        calc w a * w b * pairRect N (weight (d:ℝ)) a b
            ≤ w a * w b * ((1 / ((d:ℝ)-1)) * ∑ i : Fin d,
                pairRect N (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0) a b) := h1
          _ = _ := by rw [← mul_sum]; ring
    _ = ENNReal.ofReal (1 / ((d:ℝ)-1)) * ∑ i : Fin d, ∑' a, ∑' b, ENNReal.ofReal
          (w a * w b * pairRect N (fun k => if k i = 0 then weight ((d:ℝ)-1) k else 0) a b) := by
        simp_rw [ENNReal.tsum_mul_left]
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        simp_rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]

#print axioms weightedEnergyENN_eq_pairs
#print axioms countable_mixture_comparison_enn_direct

end BecknerOnofri.V2.Reaudit.Mixtures
