import Legacy.BecknerOnofri.TensorBernsteinCoefficients
import Mathlib.Data.Nat.Factorial.BigOperators

/-! The actual binomial normalization in tensor Bernstein coefficients. -/
noncomputable section
open Finset Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.TensorBernsteinCoefficientLimits
open FiniteDifferences

/-- Scalar normalization, expressed as a finite product; no asymptotic estimate is assumed. -/
theorem choose_normalized_eq_product {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) :
    (m.choose k : ℝ) * (1 / (m : ℝ)) ^ k =
      (∏ r ∈ range k, (1 - (r : ℝ) / (m : ℝ))) / (k.factorial : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hk0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hc : (k.factorial : ℝ) * (m.choose k : ℝ) =
      ∏ r ∈ range k, ((m : ℝ) - (r : ℝ)) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply prod_congr rfl
    intro r hr
    rw [Nat.cast_sub (le_trans (le_of_lt (mem_range.mp hr)) hk)]
  have hp : (∏ r ∈ range k, (1 - (r : ℝ) / (m : ℝ))) =
      (∏ r ∈ range k, ((m : ℝ) - (r : ℝ))) * (1 / (m : ℝ)) ^ k := by
    calc
      _ = ∏ r ∈ range k, (((m : ℝ) - (r : ℝ)) * (1 / (m : ℝ))) := by
        apply prod_congr rfl
        intro r hr
        field_simp
      _ = _ := by rw [prod_mul_distrib, prod_const, card_range]
  rw [hp, ← hc]
  field_simp

/-- For a fixed order, the true binomial coefficient has the factorial normalization. -/
theorem choose_normalized_tendsto (k : ℕ) :
    Tendsto (fun m : ℕ => (m.choose k : ℝ) * (1 / (m : ℝ)) ^ k)
      atTop (𝓝 (1 / (k.factorial : ℝ))) := by
  have hp : Tendsto (fun m : ℕ => ∏ r ∈ range k, (1 - (r : ℝ) / (m : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    have hf (r : ℕ) : Tendsto (fun m : ℕ => (1 : ℝ) - (r : ℝ) * (1 / (m : ℝ)))
        atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub
        (tendsto_one_div_atTop_nhds_zero_nat.const_mul (r : ℝ)))
    simpa only [div_eq_mul_inv, one_mul, prod_const_one] using
      (tendsto_finsetProd (range k) (fun r _ => hf r))
  apply (hp.div_const (k.factorial : ℝ)).congr'
  filter_upwards [eventually_ge_atTop (max k 1)] with m hm
  exact (choose_normalized_eq_product (by omega) (by omega)).symm

/-- The exact scalar multiplying the scaled rectangular difference. -/
def normalization {d : ℕ} (m : ℕ) (alpha : Index d) : ℝ :=
  (∏ i, (m.choose (alpha i) : ℝ)) * (1 / (m : ℝ)) ^ degree alpha

theorem normalization_eq_prod {d : ℕ} (m : ℕ) (alpha : Index d) :
    normalization m alpha = ∏ i, (m.choose (alpha i) : ℝ) * (1 / (m : ℝ)) ^ (alpha i) := by
  rw [normalization, prod_mul_distrib, prod_pow_eq_pow_sum]
  rfl

theorem normalization_nonneg {d : ℕ} (m : ℕ) (alpha : Index d) :
    0 ≤ normalization m alpha := by
  unfold normalization
  positivity

/-- No lower bound on m is needed for the sign; the limit includes every multiindex. -/
theorem normalization_tendsto {d : ℕ} (alpha : Index d) :
    Tendsto (fun m => normalization m alpha) atTop
      (𝓝 (1 / (∏ i, ((alpha i).factorial : ℝ)))) := by
  simp_rw [normalization_eq_prod]
  have h := tendsto_finsetProd univ (fun i _ => choose_normalized_tendsto (alpha i))
  simpa only [one_div, prod_inv_distrib] using h

theorem normalization_succ_tendsto {d : ℕ} (alpha : Index d) :
    Tendsto (fun m => normalization (m + 1) alpha) atTop
      (𝓝 (1 / (∏ i, ((alpha i).factorial : ℝ)))) :=
  (normalization_tendsto alpha).comp (tendsto_add_atTop_nat 1)

/-- The fixed multiindex eventually lies inside the tensor Bernstein degree box. -/
theorem eventually_in_box {d : ℕ} (alpha : Index d) :
    ∀ᶠ m : ℕ in atTop, ∀ i, alpha i ≤ m := by
  filter_upwards [eventually_ge_atTop (degree alpha)] with m hm i
  exact le_trans (single_le_sum (fun j _ => Nat.zero_le (alpha j)) (mem_univ i)) hm

theorem eventually_in_succ_box {d : ℕ} (alpha : Index d) :
    ∀ᶠ m : ℕ in atTop, ∀ i, alpha i ≤ m + 1 := by
  filter_upwards [eventually_in_box alpha] with m hm i
  exact (hm i).trans (Nat.le_succ m)

#print axioms normalization_tendsto
#print axioms normalization_succ_tendsto
end Legacy.BecknerOnofri.TensorBernsteinCoefficientLimits
