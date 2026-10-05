import Legacy.BecknerOnofri.TensorBernstein
import Legacy.BecknerOnofri.FiniteDifferenceDefs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.MvPolynomial.Coeff

/-! Exact coefficient algebra for the actual tensor Bernstein polynomials. -/
noncomputable section
open Finset
open scoped BigOperators Polynomial
namespace Legacy.BecknerOnofri.TensorBernsteinCoefficients
open TensorBernstein
set_option maxHeartbeats 800000

private theorem coeff_one_sub_X_pow (n a : ℕ) :
    ((1-Polynomial.X : ℝ[X])^n).coeff a = (-1:ℝ)^a*(n.choose a:ℝ) := by
  have hp (k : ℕ) : (-(Polynomial.X : ℝ[X]))^k = (-1:ℝ)^k • Polynomial.X^k := by
    rw [← smul_pow, neg_one_smul]
  rw [sub_eq_add_neg, add_comm, add_pow]
  simp only [one_pow, mul_one, Polynomial.finsetSum_coeff]
  simp_rw [hp, Polynomial.coeff_mul_natCast, Polynomial.coeff_smul, Polynomial.coeff_X_pow]
  rw [sum_eq_single a]
  · simp
  · intro b hb hba
    simp [Ne.symm hba]
  · intro ha
    have hna : n < a := by simp only [mem_range] at ha; omega
    simp [Nat.choose_eq_zero_of_lt hna]

/-- The univariate coefficient identity, including coefficients outside the degree. -/
theorem basis_coefficient (m j a : ℕ) :
    (bernsteinPolynomial ℝ m j).coeff a =
      (m.choose a:ℝ)*(a.choose j:ℝ)*(-1:ℝ)^(a-j) := by
  rw [bernsteinPolynomial, mul_assoc, ← Polynomial.C_eq_natCast,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs with hja
  · rw [coeff_one_sub_X_pow]
    have h : (m.choose a:ℝ)*(a.choose j:ℝ) =
        (m.choose j:ℝ)*((m-j).choose (a-j):ℝ) := by
      exact_mod_cast Nat.choose_mul hja
    rw [h]
    ring
  · have haj : a < j := Nat.lt_of_not_ge hja
    simp [Nat.choose_eq_zero_of_lt haj]

private theorem basis_natDegree_le (m j : ℕ) : (bernsteinPolynomial ℝ m j).natDegree ≤ m := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro a ha
  rw [basis_coefficient]
  simp [Nat.choose_eq_zero_of_lt ha]

/-- Expansion of a single Bernstein factor at an actual multivariate variable. -/
theorem basis_expansion {d : ℕ} (m j : ℕ) (i : Fin d) :
    (MvPolynomial.C (m.choose j:ℝ) * MvPolynomial.X i^j *
      (1-MvPolynomial.X i)^(m-j)) =
    ∑ a : Fin (m+1), MvPolynomial.C
      ((m.choose a:ℝ)*(a.val.choose j:ℝ)*(-1:ℝ)^(a.val-j)) * MvPolynomial.X i^a.val := by
  have h := (bernsteinPolynomial ℝ m j).as_sum_range_C_mul_X_pow'
    (Nat.lt_succ_of_le (basis_natDegree_le m j))
  have he := congrArg (fun p : ℝ[X] => Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) p) h
  simp only [map_sum, map_mul, map_pow, basis_coefficient, Polynomial.aeval_C,
    Polynomial.aeval_X] at he
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => MvPolynomial.C
    ((m.choose a:ℝ)*(a.choose j:ℝ)*(-1:ℝ)^(a-j))*MvPolynomial.X i^a) (m+1)]
  simpa [bernsteinPolynomial] using he

private theorem indicator_eq_iff {d m : ℕ} (alpha : Fin d →₀ ℕ) (a : Grid d m) :
    alpha = Finsupp.indicator univ (fun i _ => (a i).val) ↔
      ∀ i, alpha i = (a i).val := by
  constructor
  · intro h i
    simpa using congrArg (fun b : Fin d →₀ ℕ => b i) h
  · intro h
    ext i
    simpa using h i

private theorem coefficient_grid_expansion {d m : ℕ}
    (c : Fin d → Fin (m+1) → ℝ) (alpha : Fin d →₀ ℕ)
    (ha : ∀ i, alpha i ≤ m) :
    MvPolynomial.coeff alpha (∑ a : Grid d m,
      MvPolynomial.C (∏ i, c i (a i)) * ∏ i, (MvPolynomial.X i)^((a i).val)) =
      ∏ i, c i ⟨alpha i, Nat.lt_succ_of_le (ha i)⟩ := by
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_prod_X_pow, indicator_eq_iff]
  rw [sum_eq_single (fun i => (⟨alpha i, Nat.lt_succ_of_le (ha i)⟩ : Fin (m+1)))]
  · simp
  · intro a ha' hne
    have hn : ¬ ∀ i, alpha i = (a i).val := by
      intro h
      apply hne
      funext i
      exact Fin.ext (h i).symm
    simp [hn]
  · simp

private theorem coefficient_grid_expansion_outside {d m : ℕ}
    (c : Fin d → Fin (m+1) → ℝ) (alpha : Fin d →₀ ℕ)
    (ha : ¬ ∀ i, alpha i ≤ m) :
    MvPolynomial.coeff alpha (∑ a : Grid d m,
      MvPolynomial.C (∏ i, c i (a i)) * ∏ i, (MvPolynomial.X i)^((a i).val)) = 0 := by
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_prod_X_pow, indicator_eq_iff]
  apply sum_eq_zero
  intro a ha'
  have hn : ¬ ∀ i, alpha i = (a i).val := by
    intro h
    exact ha (fun i => (h i).symm ▸ (a i).is_le)
  simp [hn]

private theorem product_basis_expansion {d m : ℕ} (j : Grid d m) :
    (∏ i : Fin d, (MvPolynomial.C (m.choose (j i):ℝ) * MvPolynomial.X i^(j i).val *
      (1-MvPolynomial.X i)^(m-(j i).val))) =
    ∑ a : Grid d m, MvPolynomial.C
      (∏ i, ((m.choose (a i):ℝ)*((a i).val.choose (j i):ℝ)*(-1:ℝ)^((a i).val-(j i).val))) *
        ∏ i, MvPolynomial.X i^(a i).val := by
  simp_rw [basis_expansion]
  rw [Fintype.prod_sum (fun (i : Fin d) (a : Fin (m+1)) =>
    MvPolynomial.C ((m.choose a:ℝ)*(a.val.choose (j i):ℝ)*(-1:ℝ)^(a.val-(j i).val)) *
      MvPolynomial.X i^a.val)]
  apply sum_congr rfl
  intro a ha
  rw [prod_mul_distrib, map_prod]

/-- Coefficients of the tensor product of separate-variable Bernstein factors. -/
theorem product_basis_coefficient {d m : ℕ} (j : Grid d m) (alpha : Fin d →₀ ℕ) :
    MvPolynomial.coeff alpha
      (∏ i : Fin d, (MvPolynomial.C (m.choose (j i):ℝ) * MvPolynomial.X i^(j i).val *
        (1-MvPolynomial.X i)^(m-(j i).val))) =
      ∏ i, (m.choose (alpha i):ℝ)*((alpha i).choose (j i):ℝ)*(-1:ℝ)^(alpha i-(j i).val) := by
  rw [product_basis_expansion]
  by_cases ha : ∀ i, alpha i ≤ m
  · exact coefficient_grid_expansion (fun (i : Fin d) (a : Fin (m+1)) =>
      (m.choose a:ℝ)*(a.val.choose (j i):ℝ)*(-1:ℝ)^(a.val-(j i).val)) alpha ha
  · rw [coefficient_grid_expansion_outside (fun (i : Fin d) (a : Fin (m+1)) =>
      (m.choose a:ℝ)*(a.val.choose (j i):ℝ)*(-1:ℝ)^(a.val-(j i).val)) alpha ha]
    push Not at ha
    obtain ⟨i, hi⟩ := ha
    symm
    apply prod_eq_zero (mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]

/-- Actual coefficient formula before shrinking the grid to the multiindex rectangle. -/
theorem polynomial_coefficient_grid {d : ℕ} (m : ℕ) (f : Cube d → ℝ) (alpha : Fin d →₀ ℕ) :
    MvPolynomial.coeff alpha (polynomial m f) =
      ∑ j : Grid d m, f (point j) *
        ∏ i, (m.choose (alpha i):ℝ)*((alpha i).choose (j i):ℝ)*(-1:ℝ)^(alpha i-(j i).val) := by
  unfold polynomial
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_C_mul, product_basis_coefficient]

theorem polynomial_coefficient_outside {d : ℕ} (m : ℕ) (f : Cube d → ℝ)
    (alpha : Fin d →₀ ℕ) (ha : ¬ ∀ i, alpha i ≤ m) :
    MvPolynomial.coeff alpha (polynomial m f) = 0 := by
  rw [polynomial_coefficient_grid]
  push Not at ha
  obtain ⟨i, hi⟩ := ha
  apply sum_eq_zero
  intro j hj
  have hz : (∏ l, (m.choose (alpha l):ℝ)*((alpha l).choose (j l):ℝ)*
      (-1:ℝ)^(alpha l-(j l).val)) = 0 := by
    apply prod_eq_zero (mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  rw [hz, mul_zero]

/-- Terms above the multiindex vanish, so the large tensor grid reduces to its rectangle. -/
private theorem grid_sum_eq_difference {d m : ℕ} (alpha : Fin d →₀ ℕ)
    (ha : ∀ i, alpha i ≤ m) (f : (Fin d → ℝ) → ℝ) :
    (∑ j : Grid d m,
      (∏ i, (-1:ℝ)^(alpha i-(j i).val)*((alpha i).choose (j i):ℝ)) *
        f (fun i => ((j i).val:ℝ)/(m:ℝ))) =
      FiniteDifferences.rectangularDifference alpha (1/(m:ℝ)) f 0 := by
  let emb : FiniteDifferences.DifferenceGrid alpha → Grid d m :=
    fun j i => ⟨(j i).val, lt_of_lt_of_le (j i).isLt (Nat.add_le_add_right (ha i) 1)⟩
  have hinj : Function.Injective emb := by
    intro j k h
    funext i
    apply Fin.ext
    exact congrArg (fun z : Fin (m+1) => z.val) (congrFun h i)
  unfold FiniteDifferences.rectangularDifference
  symm
  apply Fintype.sum_of_injective emb hinj
  · intro j hj
    have hn : ¬ ∀ i, (j i).val ≤ alpha i := by
      intro h
      apply hj
      refine ⟨(fun i => ⟨(j i).val, Nat.lt_succ_of_le (h i)⟩), ?_⟩
      funext i
      rfl
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    have hz : (∏ l, (-1:ℝ)^(alpha l-(j l).val)*((alpha l).choose (j l):ℝ)) = 0 := by
      apply prod_eq_zero (mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hz, zero_mul]
  · intro j
    dsimp only [emb]
    simp only [zero_add, mul_one_div]

/-- Exact coefficient identity with the shared, actual rectangular forward difference.
No differentiability or sign hypothesis is used, and zero degree is also valid. -/
theorem polynomial_coefficient_difference {d : ℕ} (m : ℕ)
    (f : (Fin d → ℝ) → ℝ) (alpha : Fin d →₀ ℕ) (ha : ∀ i, alpha i ≤ m) :
    MvPolynomial.coeff alpha (polynomial m (fun y => f (fun i => (y i:ℝ)))) =
      (∏ i, (m.choose (alpha i):ℝ)) *
        FiniteDifferences.rectangularDifference alpha (1/(m:ℝ)) f 0 := by
  rw [polynomial_coefficient_grid]
  calc
    _ = (∏ i, (m.choose (alpha i):ℝ)) *
        ∑ j : Grid d m,
          (∏ i, (-1:ℝ)^(alpha i-(j i).val)*((alpha i).choose (j i):ℝ)) *
            f (fun i => ((j i).val:ℝ)/(m:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hf : f (fun i => (point j i:ℝ)) =
          f (fun i => ((j i).val:ℝ)/(m:ℝ)) := rfl
      rw [hf]
      have hp : (∏ i, (m.choose (alpha i):ℝ)*((alpha i).choose (j i):ℝ)*
          (-1:ℝ)^(alpha i-(j i).val)) =
          (∏ i, (m.choose (alpha i):ℝ)) *
            ∏ i, (-1:ℝ)^(alpha i-(j i).val)*((alpha i).choose (j i):ℝ) := by
        rw [← prod_mul_distrib]
        apply prod_congr rfl
        intro i hi
        ring
      rw [hp]
      ring
    _ = _ := by rw [grid_sum_eq_difference alpha ha f]

#print axioms polynomial_coefficient_difference
#print axioms polynomial_coefficient_outside
end Legacy.BecknerOnofri.TensorBernsteinCoefficients
