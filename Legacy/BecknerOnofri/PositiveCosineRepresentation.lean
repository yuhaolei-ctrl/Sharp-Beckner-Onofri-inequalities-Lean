module

public import Legacy.BecknerOnofri.CountableCosineMixture
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-! Normalize a positive cosine-monomial expansion into a genuine countable
probability mixture. Coefficient summability supplies the uniform majorant. -/

noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators

namespace Legacy.BecknerOnofri.PositiveCosineRepresentation
open CosineMixture

def coordinate (x : UnitAddCircle) : ℝ := Complex.normSq (1 + fourier 1 x) / 4

theorem coordinate_mem (x : UnitAddCircle) : coordinate x ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : ‖1 + fourier 1 x‖ ≤ (2 : ℝ) := by
    have h := norm_add_le (1 : ℂ) (fourier 1 x)
    have hf : ‖fourier 1 x‖ = 1 := Circle.norm_coe _
    simpa only [norm_one, hf, one_add_one_eq_two] using h
  have hq : Complex.normSq (1 + fourier 1 x) ≤ 4 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (1 + fourier 1 x)]
  constructor
  · exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  · exact (div_le_one (by norm_num : (0 : ℝ) < 4)).mpr hq

def cube {d : ℕ} (x : Torus d) : Fin d → unitInterval :=
  fun i => ⟨coordinate (x i), coordinate_mem (x i)⟩

def monomial {d : ℕ} (N : Fin d → ℕ) (x : Torus d) : ℝ :=
  ∏ i, coordinate (x i) ^ N i

theorem tensor_zero_pos {d : ℕ} (N : Fin d → ℕ) : 0 < tensor N 0 := by
  apply Finset.prod_pos
  intro i hi
  have hc : (0 : ℝ) < ((2 * N i).choose (N i) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : N i ≤ 2 * N i)
  change 0 < Complex.normSq (1 + fourier 1 0) ^ N i / ((2 * N i).choose (N i) : ℝ)
  rw [fourier_eval_zero, show Complex.normSq ((1 : ℂ) + 1) = 4 by norm_num [Complex.normSq_apply]]
  exact div_pos (pow_pos (by norm_num) _) hc

theorem tensor_zero_ge_one {d : ℕ} (N : Fin d → ℕ) : 1 ≤ tensor N 0 := by
  have h := integral_mono (tensor_integrable N)
    (integrable_const (tensor N 0) : Integrable (fun _ : Torus d => tensor N 0) (torusMeasure d))
    (CosineMixtureApproximation.tensor_le_zero N)
  simpa only [tensor_mass, integral_const, probReal_univ, one_smul] using h

theorem tensor_eq_monomial {d : ℕ} (N : Fin d → ℕ) (x : Torus d) :
    tensor N x = tensor N 0 * monomial N x := by
  unfold tensor monomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  change Complex.normSq (1 + fourier 1 (x i)) ^ N i / ((2 * N i).choose (N i) : ℝ) =
    (Complex.normSq (1 + fourier 1 0) ^ N i / ((2 * N i).choose (N i) : ℝ)) *
      (Complex.normSq (1 + fourier 1 (x i)) / 4) ^ N i
  rw [fourier_eval_zero, show Complex.normSq ((1 : ℂ) + 1) = 4 by norm_num [Complex.normSq_apply], div_pow]
  have hc : ((2 * N i).choose (N i) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : N i ≤ 2 * N i)).ne'
  field_simp


def weights {d : ℕ} (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (n : ℕ) : ℝ :=
  c n / tensor (N n) 0

theorem weights_nonneg {d : ℕ} (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hc : ∀ n, 0 ≤ c n) (n : ℕ) : 0 ≤ weights c N n :=
  div_nonneg (hc n) (tensor_zero_pos _).le

theorem weighted_tensor {d : ℕ} (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (n : ℕ) (x : Torus d) :
    weights c N n * tensor (N n) x = c n * monomial (N n) x := by
  rw [tensor_eq_monomial, weights]
  field_simp [(tensor_zero_pos (N n)).ne']

theorem weights_summable {d : ℕ} (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hc : ∀ n, 0 ≤ c n) (hs : Summable c) : Summable (weights c N) := by
  apply Summable.of_nonneg_of_le (weights_nonneg c N hc) _ hs
  intro n
  exact div_le_self (hc n) (tensor_zero_ge_one (N n))

theorem weights_majorant_summable {d : ℕ} (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hs : Summable c) : Summable (fun n => weights c N n * tensor (N n) 0) := by
  simpa only [weights, div_mul_cancel₀ _ (tensor_zero_pos _).ne'] using hs

/-- The unit mass of the actual density, not coefficient mass at the corner,
is what normalizes the cosine-mixture probability weights. -/
theorem weights_hasSum_one {d : ℕ} (r : ProbabilityDensity d)
    (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (heq : ∀ x, r.value x = ∑' n, c n * monomial (N n) x) :
    HasSum (weights c N) 1 := by
  have hw := weights_nonneg c N hc
  have hi (n : ℕ) : Integrable (fun x => weights c N n * tensor (N n) x) (torusMeasure d) :=
    (tensor_integrable _).const_mul _
  have hint (n : ℕ) : (∫ x, ‖weights c N n * tensor (N n) x‖ ∂torusMeasure d) = weights c N n := by
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hw n) (tensor_nonneg _ _))]
    rw [integral_const_mul, tensor_mass, mul_one]
  have hsum : Summable (fun n => ∫ x, ‖weights c N n * tensor (N n) x‖ ∂torusMeasure d) := by
    simpa only [hint] using weights_summable c N hc hs
  have h := integral_tsum_of_summable_integral_norm hi hsum
  simp only [integral_const_mul, tensor_mass, mul_one] at h
  simp_rw [weighted_tensor, ← heq] at h
  rw [r.mass] at h
  exact h ▸ (weights_summable c N hc hs).hasSum

theorem density_eq_countable_mixture {d : ℕ} (r : ProbabilityDensity d)
    (c : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (heq : ∀ x, r.value x = ∑' n, c n * monomial (N n) x) :
    r.value = CosineMixtureApproximation.rho (weights c N) N := by
  funext x
  simp_rw [CosineMixtureApproximation.rho, weighted_tensor]
  exact heq x

#print axioms weights_hasSum_one
#print axioms density_eq_countable_mixture
end Legacy.BecknerOnofri.PositiveCosineRepresentation
