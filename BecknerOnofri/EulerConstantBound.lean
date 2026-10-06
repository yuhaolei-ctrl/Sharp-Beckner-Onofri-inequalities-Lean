module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Tactic

@[expose] public section

/-! Exact rational lower bound for the actual Euler--Mascheroni constant.
All finite integer arithmetic and exponential Taylor bounds are kernel checked. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace BecknerOnofri.HighDim.EulerConstantBound

def floorSum (N B : ℕ) : ℕ := ∑ i∈Finset.range N,B/(i+1)

theorem floorSum_le_harmonic (N : ℕ) {B : ℕ} (hB : 0<B) :
    (floorSum N B : ℝ)/(B:ℝ)≤(harmonic N : ℝ) := by
  have hBr : (0:ℝ)<B := Nat.cast_pos.mpr hB
  unfold floorSum harmonic
  simp only [Nat.cast_sum,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hi : (0:ℝ)<(i+1:ℕ) := by positivity
  rw [inv_eq_one_div,div_le_div_iff₀ hBr hi,one_mul]
  exact_mod_cast Nat.div_mul_le_self B (i+1)

/-- The exact integer computation underlying the harmonic-number lower bound. -/
theorem floorSum_ten_thousand : floorSum 10000 1000000000=9787601186 := by
  decide

theorem harmonic_ten_thousand_lower : (97876/10000:ℝ)≤(harmonic 10000 : ℝ) := by
  have hh := floorSum_le_harmonic 10000 (B:=1000000000) (by norm_num)
  rw [floorSum_ten_thousand] at hh
  norm_num only [Nat.cast_ofNat] at hh
  linarith

/-- Twenty-four nonnegative Taylor terms suffice for this precise logarithm comparison. -/
theorem log_ten_thousand_one_upper : Real.log 10001<(18421/2000:ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  apply lt_of_lt_of_le _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤18421/2000) 24)
  norm_num [Finset.sum_range_succ,Nat.factorial_succ]

theorem euler_lower : (5771/10000:ℝ)<Real.eulerMascheroniConstant := by
  have hh := harmonic_ten_thousand_lower
  have hl := log_ten_thousand_one_upper
  have he := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 10000
  norm_num only [Real.eulerMascheroniSeq,Nat.cast_ofNat] at he
  have he' : (harmonic 10000:ℝ)-Real.log 10001<Real.eulerMascheroniConstant := by
    convert! he using 1 <;> norm_num
  linarith

#print axioms floorSum_ten_thousand
#print axioms euler_lower
end BecknerOnofri.HighDim.EulerConstantBound
