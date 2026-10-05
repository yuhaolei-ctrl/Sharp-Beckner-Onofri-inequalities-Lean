module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

@[expose] public section

/-! Rational logarithm enclosures for the entropy-route numerical inputs.
These use the finite atanh sum with the analytic remainder, and an exact
power-of-two range reduction. No floating-point evaluation is trusted. -/
namespace BecknerOnofri.HighDim.EntropyLogCertificate
open scoped BigOperators

def atanhPartial (z : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1 : ℚ)
def lower (x : ℚ) (n : ℕ) : ℚ := 2*atanhPartial ((x-1)/(x+1)) n
def upper (x : ℚ) (n : ℕ) : ℚ :=
  lower x n+2*((x-1)/(x+1))^(2*n+1)/(1-((x-1)/(x+1))^2)

theorem atanhPartial_cast (z : ℚ) (n : ℕ) : (atanhPartial z n : ℝ)=
    ∑ i ∈ Finset.range n, (z : ℝ)^(2*i+1)/(2*i+1 : ℝ) := by
  simp [atanhPartial, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_mul]

theorem unit_bounds (x : ℚ) (n : ℕ) (hx : 1≤x) :
    (lower x n : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ (upper x n : ℝ) := by
  have hx' : (1 : ℝ)≤x := by exact_mod_cast hx
  let z : ℝ := ((x : ℝ)-1)/((x : ℝ)+1)
  have hz0 : 0≤z := div_nonneg (by linarith) (by linarith)
  have hz1 : z<1 := (div_lt_one (by linarith)).mpr (by linarith)
  have he : (1+z)/(1-z)=(x : ℝ) := by
    dsimp [z]
    field_simp
    <;> ring
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hup := Real.log_div_le_sum_range_add hz0 hz1 n
  rw [he] at hlo hup
  have hl : (lower x n : ℝ)=2*(∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1 : ℝ)) := by
    simp only [lower, Rat.cast_mul, Rat.cast_ofNat, atanhPartial_cast,
      Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_one]
    rfl
  have hu : (upper x n : ℝ)=(lower x n : ℝ)+2*z^(2*n+1)/(1-z^2) := by
    simp only [upper, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_sub, Rat.cast_ofNat, Rat.cast_one]
    rfl
  simp only [mul_div_assoc] at hu
  rw [hl,hu,hl]
  constructor <;> linarith

def scaledLower (x : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  lower x n + min (k*lower 2 n) (k*upper 2 n)
def scaledUpper (x : ℚ) (k : ℤ) (n : ℕ) : ℚ :=
  upper x n + max (k*lower 2 n) (k*upper 2 n)

theorem scaled_bounds (x : ℚ) (k : ℤ) (n : ℕ) (hx : 1≤x) :
    (scaledLower x k n : ℝ) ≤ Real.log ((x : ℝ)*2^k) ∧
      Real.log ((x : ℝ)*2^k) ≤ (scaledUpper x k n : ℝ) := by
  have h := unit_bounds x n hx
  have h2 := unit_bounds 2 n (by norm_num)
  have hx0 : (0 : ℝ)<x := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ)<1) hx)
  rw [Real.log_mul hx0.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  simp only [scaledLower, scaledUpper, Rat.cast_add, Rat.cast_min, Rat.cast_max,
    Rat.cast_mul, Rat.cast_intCast]
  by_cases hk : 0≤(k : ℝ)
  · have ha := mul_le_mul_of_nonneg_left h2.1 hk
    have hb := mul_le_mul_of_nonneg_left h2.2 hk
    constructor
    · exact add_le_add h.1 ((min_le_left _ _).trans ha)
    · exact add_le_add h.2 (hb.trans (le_max_right _ _))
  · have ha := mul_le_mul_of_nonpos_left h2.1 (le_of_not_ge hk)
    have hb := mul_le_mul_of_nonpos_left h2.2 (le_of_not_ge hk)
    constructor
    · exact add_le_add h.1 ((min_le_right _ _).trans hb)
    · exact add_le_add h.2 (ha.trans (le_max_left _ _))

#print axioms scaled_bounds
end BecknerOnofri.HighDim.EntropyLogCertificate
