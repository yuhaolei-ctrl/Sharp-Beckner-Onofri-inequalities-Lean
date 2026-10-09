module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Cast.Field

@[expose] public section

/-! # Lambert series to logarithms (Appendix A.1, "Lambert series -> log")

For `0 ≤ x < 1`:
`∑_{m≥1} σ_5(m) x^m / m^6 = -∑_{k≥1} k^{-6} log(1 - x^k)`,
proved by summing the nonnegative double family `x^{kj}/(k^6 j)` over `ℕ+ × ℕ+` in two ways. -/
noncomputable section
open Finset Filter ArithmeticFunction
open scoped sigma
namespace BecknerOnofri.V2.ThetaTail

/-- the nonnegative double family -/
def lambertDouble (x : ℝ) (c : ℕ+ × ℕ+) : ℝ :=
  x ^ ((c.1 : ℕ) * (c.2 : ℕ)) / (((c.1 : ℕ) : ℝ) ^ 6 * ((c.2 : ℕ) : ℝ))

lemma lambertDouble_nonneg {x : ℝ} (h0 : 0 ≤ x) (c : ℕ+ × ℕ+) : 0 ≤ lambertDouble x c := by
  unfold lambertDouble; positivity

lemma summable_lambertDouble {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Summable (lambertDouble x) := by
  have hs := summable_prod_mul_pow 0 (r := x) (by simpa [abs_of_nonneg h0] using h1)
  refine Summable.of_nonneg_of_le (lambertDouble_nonneg h0) (fun c => ?_) hs
  unfold lambertDouble
  simp only [pow_zero, one_mul]
  have h1 : (1 : ℝ) ≤ ((c.1 : ℕ) : ℝ) ^ 6 * ((c.2 : ℕ) : ℝ) := by
    have a : (1 : ℝ) ≤ ((c.1 : ℕ) : ℝ) := by exact_mod_cast c.1.pos
    have b : (1 : ℝ) ≤ ((c.2 : ℕ) : ℝ) := by exact_mod_cast c.2.pos
    calc (1 : ℝ) = 1 ^ 6 * 1 := by norm_num
      _ ≤ _ := by gcongr
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ x ^ ((c.1 : ℕ) * (c.2 : ℕ)) := pow_nonneg h0 _
  nlinarith

lemma hasSum_inner {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ+) :
    HasSum (fun j : ℕ+ => lambertDouble x (k, j))
      ((-Real.log (1 - x ^ (k : ℕ))) / ((k : ℕ) : ℝ) ^ 6) := by
  have hy0 : 0 ≤ x ^ (k : ℕ) := pow_nonneg h0 _
  have hy1 : x ^ (k : ℕ) < 1 := pow_lt_one₀ h0 h1 k.ne_zero
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := x ^ (k : ℕ))
    (by rwa [abs_of_nonneg hy0])
  have h2 := h.div_const (((k : ℕ) : ℝ) ^ 6)
  refine (Equiv.hasSum_iff (Equiv.pnatEquivNat.symm)).1 ?_
  convert h2 using 1
  ext n
  simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, lambertDouble]
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  rw [pow_mul]
  push_cast
  field_simp

lemma lambert_fiber_sum (x : ℝ) (m : ℕ+) :
    ∑ c : Nat.divisorsAntidiagonal (m : ℕ), lambertDouble x (divisorsAntidiagonalFactors m c)
      = (σ 5 m : ℝ) * x ^ (m : ℕ) / ((m : ℕ) : ℝ) ^ 6 := by
  have hc : ∀ c : Nat.divisorsAntidiagonal (m : ℕ), lambertDouble x (divisorsAntidiagonalFactors m c)
      = x ^ (m : ℕ) / (((c.1.1 : ℕ) : ℝ) ^ 6 * ((c.1.2 : ℕ) : ℝ)) := by
    intro c
    unfold lambertDouble
    have e : ((divisorsAntidiagonalFactors m c).1 : ℕ) * ((divisorsAntidiagonalFactors m c).2 : ℕ)
        = (m : ℕ) := divisorsAntidiagonalFactors_eq c
    rw [e]
    rfl
  simp only [hc]
  rw [Finset.sum_coe_sort (Nat.divisorsAntidiagonal (m : ℕ))
    (fun p : ℕ × ℕ => x ^ (m : ℕ) / ((p.1 : ℝ) ^ 6 * (p.2 : ℝ)))]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => x ^ (m : ℕ) / ((a : ℝ) ^ 6 * (b : ℝ)))]
  rw [ArithmeticFunction.sigma_apply]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div,
    ← Nat.sum_div_divisors (m : ℕ) (fun d => (d : ℝ) ^ 5 * x ^ (m : ℕ) / ((m : ℕ) : ℝ) ^ 6)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d ∣ (m : ℕ) := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd
    exact_mod_cast this.ne'
  have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hcast : (((m : ℕ) / d : ℕ) : ℝ) = ((m : ℕ) : ℝ) / d := Nat.cast_div hdm hd0
  have hq0 : ((((m : ℕ) / d : ℕ) : ℕ) : ℝ) ≠ 0 := by
    rw [hcast]; exact div_ne_zero hm0 hd0
  rw [hcast]
  field_simp

/-- `∑_{m≥1} σ_5(m) x^m/m^6 = -∑_{k≥1} k^{-6} log(1-x^k)`, as a `HasSum` (so absolutely
summable, all terms being nonnegative). -/
theorem hasSum_lambert_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    HasSum (fun m : ℕ+ => (σ 5 m : ℝ) * x ^ (m : ℕ) / ((m : ℕ) : ℝ) ^ 6)
      (∑' k : ℕ+, (-Real.log (1 - x ^ (k : ℕ))) / ((k : ℕ) : ℝ) ^ 6) := by
  have hu := summable_lambertDouble h0 h1
  have h2 : HasSum (fun k : ℕ+ => (-Real.log (1 - x ^ (k : ℕ))) / ((k : ℕ) : ℝ) ^ 6)
      (∑' c, lambertDouble x c) :=
    hu.hasSum.prod_fiberwise (fun k => hasSum_inner h0 h1 k)
  have hA : HasSum (lambertDouble x) (∑' k : ℕ+, (-Real.log (1 - x ^ (k : ℕ))) / ((k : ℕ) : ℝ) ^ 6) := by
    rw [h2.tsum_eq]; exact hu.hasSum
  have hB := (sigmaAntidiagonalEquivProd.hasSum_iff (f := lambertDouble x)).2 hA
  refine hB.sigma (fun m => ?_)
  have := hasSum_fintype (fun c : Nat.divisorsAntidiagonal (m : ℕ) =>
    (lambertDouble x ∘ sigmaAntidiagonalEquivProd) ⟨m, c⟩)
  convert this using 1
  rw [← lambert_fiber_sum x m]
  rfl

theorem tsum_lambert_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    ∑' m : ℕ+, (σ 5 m : ℝ) * x ^ (m : ℕ) / ((m : ℕ) : ℝ) ^ 6
      = ∑' k : ℕ+, (-Real.log (1 - x ^ (k : ℕ))) / ((k : ℕ) : ℝ) ^ 6 :=
  (hasSum_lambert_log h0 h1).tsum_eq

/-- the logarithmic side is summable too (nonnegative terms) -/
theorem summable_neg_log_terms {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Summable (fun k : ℕ+ => (-Real.log (1 - x ^ (k : ℕ))) / ((k : ℕ) : ℝ) ^ 6) :=
  (summable_lambertDouble h0 h1).hasSum.prod_fiberwise (fun k => hasSum_inner h0 h1 k) |>.summable

end BecknerOnofri.V2.ThetaTail
