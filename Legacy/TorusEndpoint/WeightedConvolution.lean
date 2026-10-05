module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

/-!
# Finite weighted Cauchy–Schwarz and convolution

The ambient index types need not be finite. All sums are over explicit finite
sets. Input weights are positive on those sets, and output weights may
dominate, rather than equal, the finite fiber masses. This is the form needed
for finitely supported Fourier polynomials whose coefficient-space weights
have further positive contributions outside the polynomial supports.

No endpoint inequality, exponential coefficient identity, or numerical
certificate is assumed or asserted in this module.
-/

open scoped BigOperators

namespace Legacy.TorusEndpoint

variable {ι κ η : Type*}

/-- Finite real weighted Cauchy–Schwarz, with positivity only on the summation set. -/
theorem real_weighted_sum_sq_le (s : Finset ι) (x a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, x i) ^ 2 ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, x i ^ 2 / a i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := x) (f := fun i ↦ x i ^ 2 / a i) (g := a)
    (fun i hi ↦ div_nonneg (sq_nonneg _) (ha i hi).le)
    (fun i hi ↦ (ha i hi).le)
    (fun i hi ↦ by rw [div_mul_cancel₀ _ (ha i hi).ne'])
  simpa only [mul_comm] using h

/-- The divided real version also includes the empty finite set. -/
theorem real_weighted_sum_div_le (s : Finset ι) (x a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, x i) ^ 2 / (∑ i ∈ s, a i) ≤
      ∑ i ∈ s, x i ^ 2 / a i :=
  Finset.sq_sum_div_le_sum_sq_div s x ha

/-- The norm-valued form applies in particular to both real and complex scalars. -/
theorem weighted_norm_sum_sq_le {V : Type*} [SeminormedAddCommGroup V]
    (s : Finset ι) (z : ι → V) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, ‖z i‖ ^ 2 / a i) := by
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := by
      simpa only [pow_two] using
        mul_self_le_mul_self (norm_nonneg (∑ i ∈ s, z i)) (norm_sum_le s z)
    _ ≤ _ := real_weighted_sum_sq_le s (fun i ↦ ‖z i‖) a ha

/-- Complex weighted Cauchy–Schwarz, as a convenient scalar-specialized entry point. -/
theorem complex_weighted_sum_sq_le (s : Finset ι) (z : ι → ℂ) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤
      (∑ i ∈ s, a i) * (∑ i ∈ s, ‖z i‖ ^ 2 / a i) :=
  weighted_norm_sum_sq_le s z a ha

/-- Enlarging the output weight preserves the fiber estimate, including empty fibers. -/
theorem weighted_norm_sum_div_le {V : Type*} [SeminormedAddCommGroup V]
    (s : Finset ι) (z : ι → V) (a : ι → ℝ) (W : ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hW : 0 < W)
    (hmass : ∑ i ∈ s, a i ≤ W) :
    ‖∑ i ∈ s, z i‖ ^ 2 / W ≤ ∑ i ∈ s, ‖z i‖ ^ 2 / a i := by
  apply (div_le_iff₀ hW).2
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤
        (∑ i ∈ s, a i) * (∑ i ∈ s, ‖z i‖ ^ 2 / a i) :=
      weighted_norm_sum_sq_le s z a ha
    _ ≤ W * (∑ i ∈ s, ‖z i‖ ^ 2 / a i) :=
      mul_le_mul_of_nonneg_right hmass
        (Finset.sum_nonneg fun i hi ↦ div_nonneg (sq_nonneg _) (ha i hi).le)
    _ = (∑ i ∈ s, ‖z i‖ ^ 2 / a i) * W := mul_comm _ _

/-- The weighted squared ℓ² expression on an explicit finite set. -/
noncomputable def weightedL2Sq {V : Type*} [SeminormedAddCommGroup V]
    (s : Finset ι) (z : ι → V) (a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, ‖z i‖ ^ 2 / a i

/-- The corresponding nonnegative weighted ℓ² expression. -/
noncomputable def weightedL2 {V : Type*} [SeminormedAddCommGroup V]
    (s : Finset ι) (z : ι → V) (a : ι → ℝ) : ℝ :=
  Real.sqrt (weightedL2Sq s z a)

theorem weightedL2Sq_nonneg {V : Type*} [SeminormedAddCommGroup V]
    (s : Finset ι) (z : ι → V) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 0 ≤ weightedL2Sq s z a :=
  Finset.sum_nonneg fun i hi ↦ div_nonneg (sq_nonneg _) (ha i hi)

/-- The finite pushforward of a vector-valued array along an arbitrary index map. -/
def fiberSum {V : Type*} [AddCommMonoid V] [DecidableEq κ]
    (s : Finset ι) (f : ι → κ) (z : ι → V) (k : κ) : V :=
  ∑ i ∈ s with f i = k, z i

/-- Weighted contraction under a finite fiber aggregation. The ambient types may be infinite. -/
theorem weighted_fiber_sum_sq_le {V : Type*} [SeminormedAddCommGroup V]
    [DecidableEq κ] (s : Finset ι) (u : Finset κ)
    (f : ι → κ) (z : ι → V) (a : ι → ℝ) (W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ i ∈ s, f i ∈ u)
    (hmass : ∀ k ∈ u, ∑ i ∈ s with f i = k, a i ≤ W k) :
    weightedL2Sq u (fiberSum s f z) W ≤ weightedL2Sq s z a := by
  calc
    weightedL2Sq u (fiberSum s f z) W ≤
        ∑ k ∈ u, ∑ i ∈ s with f i = k, ‖z i‖ ^ 2 / a i := by
      apply Finset.sum_le_sum
      intro k hk
      exact weighted_norm_sum_div_le (s.filter (fun i ↦ f i = k)) z a (W k)
        (fun i hi ↦ ha i (Finset.mem_filter.mp hi).1) (hW k hk) (hmass k hk)
    _ = weightedL2Sq s z a := Finset.sum_fiberwise_of_maps_to hcover _

/-- Finite weighted fiber aggregation is also contractive before squaring. -/
theorem weighted_fiber_sum_le {V : Type*} [SeminormedAddCommGroup V]
    [DecidableEq κ] (s : Finset ι) (u : Finset κ)
    (f : ι → κ) (z : ι → V) (a : ι → ℝ) (W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ i ∈ s, f i ∈ u)
    (hmass : ∀ k ∈ u, ∑ i ∈ s with f i = k, a i ≤ W k) :
    weightedL2 u (fiberSum s f z) W ≤ weightedL2 s z a :=
  Real.sqrt_le_sqrt (weighted_fiber_sum_sq_le s u f z a W ha hW hcover hmass)

/-- Pairwise complex products aggregated by any output map satisfy the weighted product bound. -/
theorem weighted_pair_convolution_sq_le [DecidableEq κ]
    (s : Finset ι) (t : Finset η) (u : Finset κ) (f : ι × η → κ)
    (v : ι → ℂ) (w : η → ℂ) (a : ι → ℝ) (b : η → ℝ) (W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ j ∈ t, 0 < b j)
    (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ ij ∈ s ×ˢ t, f ij ∈ u)
    (hmass : ∀ k ∈ u,
      ∑ ij ∈ s ×ˢ t with f ij = k, a ij.1 * b ij.2 ≤ W k) :
    weightedL2Sq u (fiberSum (s ×ˢ t) f (fun ij ↦ v ij.1 * w ij.2)) W ≤
      weightedL2Sq s v a * weightedL2Sq t w b := by
  calc
    _ ≤ weightedL2Sq (s ×ˢ t) (fun ij ↦ v ij.1 * w ij.2)
        (fun ij ↦ a ij.1 * b ij.2) := by
      apply weighted_fiber_sum_sq_le (s ×ˢ t) u f
        (fun ij ↦ v ij.1 * w ij.2) (fun ij ↦ a ij.1 * b ij.2) W
      · intro ij hij
        exact mul_pos (ha ij.1 (Finset.mem_product.mp hij).1)
          (hb ij.2 (Finset.mem_product.mp hij).2)
      · exact hW
      · exact hcover
      · exact hmass
    _ = weightedL2Sq s v a * weightedL2Sq t w b := by
      simp only [weightedL2Sq, Finset.sum_product, Complex.norm_mul, mul_pow,
        mul_div_mul_comm, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

/-- The unsquared product bound for finite pairwise complex convolution. -/
theorem weighted_pair_convolution_le [DecidableEq κ]
    (s : Finset ι) (t : Finset η) (u : Finset κ) (f : ι × η → κ)
    (v : ι → ℂ) (w : η → ℂ) (a : ι → ℝ) (b : η → ℝ) (W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ j ∈ t, 0 < b j)
    (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ ij ∈ s ×ˢ t, f ij ∈ u)
    (hmass : ∀ k ∈ u,
      ∑ ij ∈ s ×ˢ t with f ij = k, a ij.1 * b ij.2 ≤ W k) :
    weightedL2 u (fiberSum (s ×ˢ t) f (fun ij ↦ v ij.1 * w ij.2)) W ≤
      weightedL2 s v a * weightedL2 t w b := by
  have h := Real.sqrt_le_sqrt
    (weighted_pair_convolution_sq_le s t u f v w a b W ha hb hW hcover hmass)
  simpa only [weightedL2, Real.sqrt_mul
    (weightedL2Sq_nonneg s v a (fun i hi ↦ (ha i hi).le))] using h

/-- Additive convolution is the output-map specialization `f (i,j) = i+j`. -/
theorem weighted_add_convolution_le [Add κ] [DecidableEq κ]
    (s t u : Finset κ) (v w : κ → ℂ) (a b W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ j ∈ t, 0 < b j)
    (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ ij ∈ s ×ˢ t, ij.1 + ij.2 ∈ u)
    (hmass : ∀ k ∈ u,
      ∑ ij ∈ s ×ˢ t with ij.1 + ij.2 = k, a ij.1 * b ij.2 ≤ W k) :
    weightedL2 u
      (fiberSum (s ×ˢ t) (fun ij ↦ ij.1 + ij.2) (fun ij ↦ v ij.1 * w ij.2)) W ≤
      weightedL2 s v a * weightedL2 t w b :=
  weighted_pair_convolution_le s t u (fun ij ↦ ij.1 + ij.2) v w a b W
    ha hb hW hcover hmass

/-- The same squared product bound for real arrays, obtained by the isometric real embedding. -/
theorem real_weighted_pair_convolution_sq_le [DecidableEq κ]
    (s : Finset ι) (t : Finset η) (u : Finset κ) (f : ι × η → κ)
    (v : ι → ℝ) (w : η → ℝ) (a : ι → ℝ) (b : η → ℝ) (W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ j ∈ t, 0 < b j)
    (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ ij ∈ s ×ˢ t, f ij ∈ u)
    (hmass : ∀ k ∈ u,
      ∑ ij ∈ s ×ˢ t with f ij = k, a ij.1 * b ij.2 ≤ W k) :
    weightedL2Sq u (fiberSum (s ×ˢ t) f (fun ij ↦ v ij.1 * w ij.2)) W ≤
      weightedL2Sq s v a * weightedL2Sq t w b := by
  have h := weighted_pair_convolution_sq_le s t u f
    (fun i ↦ (v i : ℂ)) (fun j ↦ (w j : ℂ)) a b W ha hb hW hcover hmass
  have hcast (k : κ) :
      fiberSum (s ×ˢ t) f (fun ij ↦ (v ij.1 : ℂ) * (w ij.2 : ℂ)) k =
        ((fiberSum (s ×ˢ t) f (fun ij ↦ v ij.1 * w ij.2) k : ℝ) : ℂ) := by
    simp only [fiberSum, ← Complex.ofReal_mul]
    exact (map_sum Complex.ofRealHom (fun ij ↦ v ij.1 * w ij.2)
      ((s ×ˢ t).filter (fun ij ↦ f ij = k))).symm
  simpa only [weightedL2Sq, hcast, Complex.norm_real] using h

/-- The unsquared finite product bound for real arrays. -/
theorem real_weighted_pair_convolution_le [DecidableEq κ]
    (s : Finset ι) (t : Finset η) (u : Finset κ) (f : ι × η → κ)
    (v : ι → ℝ) (w : η → ℝ) (a : ι → ℝ) (b : η → ℝ) (W : κ → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ j ∈ t, 0 < b j)
    (hW : ∀ k ∈ u, 0 < W k)
    (hcover : ∀ ij ∈ s ×ˢ t, f ij ∈ u)
    (hmass : ∀ k ∈ u,
      ∑ ij ∈ s ×ˢ t with f ij = k, a ij.1 * b ij.2 ≤ W k) :
    weightedL2 u (fiberSum (s ×ˢ t) f (fun ij ↦ v ij.1 * w ij.2)) W ≤
      weightedL2 s v a * weightedL2 t w b := by
  have h := Real.sqrt_le_sqrt
    (real_weighted_pair_convolution_sq_le s t u f v w a b W ha hb hW hcover hmass)
  simpa only [weightedL2, Real.sqrt_mul
    (weightedL2Sq_nonneg s v a (fun i hi ↦ (ha i hi).le))] using h

end Legacy.TorusEndpoint
