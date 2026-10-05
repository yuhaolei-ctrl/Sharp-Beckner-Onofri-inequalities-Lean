module

public import Legacy.TorusEndpoint.WeightedConvolution
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Weighted norms of actual finitely supported polynomials

The coefficients below belong to `AddMonoidAlgebra ℂ G`; multiplication is
Mathlib's algebra multiplication, not an assumed convolution identity.
Weights need only dominate the finite masses from the actual input supports.
No exponential coefficient identity or endpoint certificate is postulated.
-/

open scoped BigOperators

namespace Legacy.TorusEndpoint

variable {G : Type*}

/-- Weighted squared norm on exactly the nonzero coefficient support. -/
noncomputable def polynomialWeightedL2Sq (F : AddMonoidAlgebra ℂ G)
    (a : G → ℝ) : ℝ := weightedL2Sq F.coeff.support F.coeff a

/-- The associated nonnegative square root. -/
noncomputable def polynomialWeightedL2 (F : AddMonoidAlgebra ℂ G)
    (a : G → ℝ) : ℝ := Real.sqrt (polynomialWeightedL2Sq F a)

theorem polynomialWeightedL2Sq_nonneg (F : AddMonoidAlgebra ℂ G)
    (a : G → ℝ) (ha : ∀ k ∈ F.coeff.support, 0 ≤ a k) :
    0 ≤ polynomialWeightedL2Sq F a := weightedL2Sq_nonneg _ _ _ ha

/-- A coefficient upper bound by one converts the weighted estimate into
the unweighted coefficient square sum, ready for finite Parseval. -/
theorem polynomial_coeff_sq_sum_le_weighted (F : AddMonoidAlgebra ℂ G)
    (C : G → ℝ) (hpos : ∀ k ∈ F.coeff.support, 0 < C k)
    (hbound : ∀ k ∈ F.coeff.support, C k ≤ 1) :
    (∑ k ∈ F.coeff.support, ‖F.coeff k‖ ^ 2) ≤ polynomialWeightedL2Sq F C := by
  apply Finset.sum_le_sum
  intro k hk
  simpa only [div_one] using
    div_le_div_of_nonneg_left (sq_nonneg ‖F.coeff k‖) (hpos k hk) (hbound k hk)

/-- Extending the sum by zero coefficients does not change the expression.
No weight positivity outside the actual support is needed for this identity. -/
theorem polynomialWeightedL2Sq_eq_sum (F : AddMonoidAlgebra ℂ G)
    (a : G → ℝ) (s : Finset G) (hs : F.coeff.support ⊆ s) :
    polynomialWeightedL2Sq F a = ∑ k ∈ s, ‖F.coeff k‖ ^ 2 / a k := by
  apply Finset.sum_subset hs
  intro k _ hk
  have hz : F.coeff k = 0 := Finsupp.notMem_support_iff.mp hk
  simp [hz]

/-- The actual algebra multiplication has the required finite-fiber formula. -/
theorem polynomial_coeff_mul [Add G] [DecidableEq G]
    (F H : AddMonoidAlgebra ℂ G) (k : G) :
    (F * H).coeff k =
      fiberSum (F.coeff.support ×ˢ H.coeff.support)
        (fun ij ↦ ij.1 + ij.2) (fun ij ↦ F.coeff ij.1 * H.coeff ij.2) k := by
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum, fiberSum, Finset.sum_filter, Finset.sum_product]

/-- The squared norm inequality for actual polynomial multiplication.
Cancellation may make the output support smaller than the pair-sum set;
the proof sums only the selected fibers and drops the others nonnegatively. -/
theorem polynomialWeightedL2Sq_mul_le [Add G] [DecidableEq G]
    (F H : AddMonoidAlgebra ℂ G) (a b C : G → ℝ)
    (ha : ∀ i ∈ F.coeff.support, 0 < a i)
    (hb : ∀ j ∈ H.coeff.support, 0 < b j)
    (hC : ∀ k ∈ (F * H).coeff.support, 0 < C k)
    (hmass : ∀ k ∈ (F * H).coeff.support,
      ∑ ij ∈ F.coeff.support ×ˢ H.coeff.support with ij.1 + ij.2 = k,
        a ij.1 * b ij.2 ≤ C k) :
    polynomialWeightedL2Sq (F * H) C ≤
      polynomialWeightedL2Sq F a * polynomialWeightedL2Sq H b := by
  have hp (ij : G × G) (hij : ij ∈ F.coeff.support ×ˢ H.coeff.support) :
      0 < a ij.1 * b ij.2 :=
    mul_pos (ha _ (Finset.mem_product.mp hij).1)
      (hb _ (Finset.mem_product.mp hij).2)
  calc
    polynomialWeightedL2Sq (F * H) C ≤
        ∑ k ∈ (F * H).coeff.support,
          ∑ ij ∈ F.coeff.support ×ˢ H.coeff.support with ij.1 + ij.2 = k,
            ‖F.coeff ij.1 * H.coeff ij.2‖ ^ 2 / (a ij.1 * b ij.2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [polynomial_coeff_mul]
      exact weighted_norm_sum_div_le _ _ _ _
        (fun ij hij ↦ hp ij (Finset.mem_filter.mp hij).1) (hC k hk) (hmass k hk)
    _ = ∑ ij ∈ F.coeff.support ×ˢ H.coeff.support
          with ij.1 + ij.2 ∈ (F * H).coeff.support,
          ‖F.coeff ij.1 * H.coeff ij.2‖ ^ 2 / (a ij.1 * b ij.2) :=
      Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ ij ∈ F.coeff.support ×ˢ H.coeff.support,
          ‖F.coeff ij.1 * H.coeff ij.2‖ ^ 2 / (a ij.1 * b ij.2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro ij hij _
      exact div_nonneg (sq_nonneg _) (hp ij hij).le
    _ = polynomialWeightedL2Sq F a * polynomialWeightedL2Sq H b := by
      simp only [polynomialWeightedL2Sq, weightedL2Sq, Finset.sum_product,
        Complex.norm_mul, mul_pow, mul_div_mul_comm, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm

/-- Unsquared norm multiplicativity bound for actual polynomial multiplication. -/
theorem polynomialWeightedL2_mul_le [Add G] [DecidableEq G]
    (F H : AddMonoidAlgebra ℂ G) (a b C : G → ℝ)
    (ha : ∀ i ∈ F.coeff.support, 0 < a i)
    (hb : ∀ j ∈ H.coeff.support, 0 < b j)
    (hC : ∀ k ∈ (F * H).coeff.support, 0 < C k)
    (hmass : ∀ k ∈ (F * H).coeff.support,
      ∑ ij ∈ F.coeff.support ×ˢ H.coeff.support with ij.1 + ij.2 = k,
        a ij.1 * b ij.2 ≤ C k) :
    polynomialWeightedL2 (F * H) C ≤
      polynomialWeightedL2 F a * polynomialWeightedL2 H b := by
  have h := Real.sqrt_le_sqrt (polynomialWeightedL2Sq_mul_le F H a b C ha hb hC hmass)
  simpa only [polynomialWeightedL2, Real.sqrt_mul
    (polynomialWeightedL2Sq_nonneg F a (fun i hi ↦ (ha i hi).le))] using h

section Powers

variable [AddMonoid G] [DecidableEq G]

omit [DecidableEq G] in
@[simp] theorem polynomialWeightedL2Sq_one (a : G → ℝ) :
    polynomialWeightedL2Sq (1 : AddMonoidAlgebra ℂ G) a = 1 / a 0 := by
  have hnorm : ‖(1 : ℂ)‖ = 1 := by simpa using Complex.norm_natCast 1
  simp [polynomialWeightedL2Sq, weightedL2Sq, AddMonoidAlgebra.one_def, hnorm]

/-- Iterating the proved multiplication inequality along an explicit weight
family. Only finite support-pair domination is required at each step. -/
theorem polynomialWeightedL2Sq_pow_le
    (P : AddMonoidAlgebra ℂ G) (W : ℕ → G → ℝ)
    (hzero : W 0 0 = 1)
    (hpos : ∀ n k, k ∈ (P ^ n).coeff.support → 0 < W n k)
    (hmass : ∀ n k, k ∈ (P ^ (n + 1)).coeff.support →
      ∑ ij ∈ (P ^ n).coeff.support ×ˢ P.coeff.support with ij.1 + ij.2 = k,
        W n ij.1 * W 1 ij.2 ≤ W (n + 1) k) (n : ℕ) :
    polynomialWeightedL2Sq (P ^ n) (W n) ≤
      polynomialWeightedL2Sq P (W 1) ^ n := by
  have hP : ∀ k ∈ P.coeff.support, 0 < W 1 k := by simpa using hpos 1
  have hnonneg := polynomialWeightedL2Sq_nonneg P (W 1) (fun k hk ↦ (hP k hk).le)
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    calc
      polynomialWeightedL2Sq (P ^ (n + 1)) (W (n + 1)) ≤
          polynomialWeightedL2Sq (P ^ n) (W n) * polynomialWeightedL2Sq P (W 1) := by
        rw [pow_succ]
        apply polynomialWeightedL2Sq_mul_le (P ^ n) P (W n) (W 1) (W (n + 1))
        · exact hpos n
        · exact hP
        · simpa only [pow_succ] using hpos (n + 1)
        · simpa only [pow_succ] using hmass n
      _ ≤ polynomialWeightedL2Sq P (W 1) ^ n * polynomialWeightedL2Sq P (W 1) :=
        mul_le_mul_of_nonneg_right ih hnonneg
      _ = polynomialWeightedL2Sq P (W 1) ^ (n + 1) := (pow_succ _ _).symm

/-- Positivity and the convolution condition for a real-parameter family are
checked only at the finitely supported polynomial powers used here. -/
theorem polynomialWeightedL2Sq_pow_parameter_le
    (P : AddMonoidAlgebra ℂ G) (C : ℝ → G → ℝ) (q : ℝ)
    (hzero : C 0 0 = 1)
    (hpos : ∀ (n : ℕ) k, k ∈ (P ^ n).coeff.support → 0 < C ((n : ℝ) * q) k)
    (hmass : ∀ (n : ℕ) k, k ∈ (P ^ (n + 1)).coeff.support →
      ∑ ij ∈ (P ^ n).coeff.support ×ˢ P.coeff.support with ij.1 + ij.2 = k,
        C ((n : ℝ) * q) ij.1 * C q ij.2 ≤ C (((n : ℝ) + 1) * q) k) (n : ℕ) :
    polynomialWeightedL2Sq (P ^ n) (C ((n : ℝ) * q)) ≤
      polynomialWeightedL2Sq P (C q) ^ n := by
  simpa only [Nat.cast_zero, zero_mul, Nat.cast_one, one_mul, Nat.cast_add] using
    polynomialWeightedL2Sq_pow_le P (fun n ↦ C ((n : ℝ) * q))
      (by simpa using hzero) hpos (by simpa using hmass) n

/-- Exact separation of the constant coefficient and a polynomial with zero
constant coefficient. This is an identity, not a one-atom weight assumption. -/
theorem polynomialWeightedL2Sq_one_add_smul
    (F : AddMonoidAlgebra ℂ G) (c : ℂ) (a : G → ℝ) (hF : F.coeff 0 = 0) :
    polynomialWeightedL2Sq (1 + c • F) a =
      1 / a 0 + ‖c‖ ^ 2 * polynomialWeightedL2Sq F a := by
  have hz : 0 ∉ F.coeff.support := Finsupp.notMem_support_iff.mpr hF
  have hcoeff0 : (1 + c • F).coeff 0 = 1 := by simp [hF]
  have hcoeff (k : G) (hk : k ≠ 0) : (1 + c • F).coeff k = c * F.coeff k := by
    simp [AddMonoidAlgebra.one_def, hk, smul_eq_mul]
  have hs : (1 + c • F).coeff.support ⊆ insert 0 F.coeff.support := by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · apply Finset.mem_insert_of_mem
      by_contra hn
      have hfk : F.coeff k = 0 := Finsupp.notMem_support_iff.mp hn
      exact (Finsupp.mem_support_iff.mp hk) (by rw [hcoeff k hk0, hfk, mul_zero])
  rw [polynomialWeightedL2Sq_eq_sum _ _ _ hs, Finset.sum_insert hz, hcoeff0]
  have hnorm : ‖(1 : ℂ)‖ = 1 := by simpa using Complex.norm_natCast 1
  simp only [hnorm, one_pow]
  congr 1
  calc
    ∑ k ∈ F.coeff.support, ‖(1 + c • F).coeff k‖ ^ 2 / a k =
        ∑ k ∈ F.coeff.support, ‖c‖ ^ 2 * (‖F.coeff k‖ ^ 2 / a k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := by intro he; exact hz (he ▸ hk)
      rw [hcoeff k hk0, Complex.norm_mul, mul_pow, mul_div_assoc]
    _ = ‖c‖ ^ 2 * polynomialWeightedL2Sq F a := (Finset.mul_sum ..).symm

/-- A one-atom lower bound on the weight yields the exact first-factor bound.
The coefficient of the constant term is separated using `F.coeff 0 = 0`. -/
theorem polynomialWeightedL2Sq_one_add_scale_le
    (F : AddMonoidAlgebra ℂ G) (a C : G → ℝ) (q : ℝ)
    (hF : F.coeff 0 = 0) (hq : 0 < q) (hunit : C 0 = 1)
    (ha : ∀ k ∈ F.coeff.support, 0 < a k)
    (hone : ∀ k ∈ F.coeff.support, q * a k ≤ C k) :
    polynomialWeightedL2Sq (1 + (q : ℂ) • F) C ≤
      1 + q * polynomialWeightedL2Sq F a := by
  rw [polynomialWeightedL2Sq_one_add_smul F (q : ℂ) C hF,
    Complex.norm_of_nonneg hq.le, hunit, div_one]
  apply add_le_add_right
  calc
    q ^ 2 * polynomialWeightedL2Sq F C =
        ∑ k ∈ F.coeff.support, q ^ 2 * (‖F.coeff k‖ ^ 2 / C k) :=
      Finset.mul_sum ..
    _ ≤ ∑ k ∈ F.coeff.support, q ^ 2 * (‖F.coeff k‖ ^ 2 / (q * a k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hq (ha k hk)) (hone k hk))
        (sq_nonneg q)
    _ = q * polynomialWeightedL2Sq F a := by
      rw [polynomialWeightedL2Sq, weightedL2Sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp [hq.ne', (ha k hk).ne']

/-- The finite binomial approximants obey the bound required before taking
an exponential limit. Every hypothesis is a finite-support kernel condition;
the theorem does not assume any unproved infinite coefficient identity. -/
theorem polynomialWeightedL2Sq_binomial_le
    (F : AddMonoidAlgebra ℂ G) (a : G → ℝ) (C : ℝ → G → ℝ)
    (M : ℕ) (hM : 0 < M) (hF : F.coeff 0 = 0)
    (ha : ∀ k ∈ F.coeff.support, 0 < a k)
    (hzero : C 0 0 = 1) (hunit : C (1 / (M : ℝ)) 0 = 1)
    (hone : ∀ k ∈ F.coeff.support, (1 / (M : ℝ)) * a k ≤ C (1 / (M : ℝ)) k)
    (hpos : ∀ (n : ℕ) k,
      k ∈ ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ n).coeff.support →
        0 < C ((n : ℝ) * (1 / (M : ℝ))) k)
    (hmass : ∀ (n : ℕ) k,
      k ∈ ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ (n + 1)).coeff.support →
      ∑ ij ∈ ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ n).coeff.support ×ˢ
          (1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F).coeff.support with ij.1 + ij.2 = k,
        C ((n : ℝ) * (1 / (M : ℝ))) ij.1 * C (1 / (M : ℝ)) ij.2 ≤
          C (((n : ℝ) + 1) * (1 / (M : ℝ))) k) :
    polynomialWeightedL2Sq
      ((1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) ^ M) (C 1) ≤
      (1 + polynomialWeightedL2Sq F a / (M : ℝ)) ^ M := by
  have hMr : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hq : 0 < 1 / (M : ℝ) := one_div_pos.mpr hMr
  have hbase := polynomialWeightedL2Sq_one_add_scale_le F a (C (1 / (M : ℝ)))
    (1 / (M : ℝ)) hF hq hunit ha hone
  have hPpos : ∀ k ∈ (1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F).coeff.support,
      0 ≤ C (1 / (M : ℝ)) k := by
    simpa only [pow_one, Nat.cast_one, one_mul] using fun k hk ↦ (hpos 1 k hk).le
  have hpower := polynomialWeightedL2Sq_pow_parameter_le
    (1 + ((1 / (M : ℝ) : ℝ) : ℂ) • F) C (1 / (M : ℝ)) hzero hpos hmass M
  have hmul : (M : ℝ) * (1 / (M : ℝ)) = 1 := by field_simp
  rw [hmul] at hpower
  exact hpower.trans (by
    simpa only [one_div, mul_comm ((M : ℝ)⁻¹), ← div_eq_mul_inv] using
      pow_le_pow_left₀ (polynomialWeightedL2Sq_nonneg _ _ hPpos) hbase M)

end Powers

end Legacy.TorusEndpoint
