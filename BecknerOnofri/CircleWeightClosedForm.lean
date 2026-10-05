import BecknerOnofri.CircleWeightSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! The logarithmic formula used for the large-mean scalar certificates,
proved by splitting the actual logarithm series. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.CircleScalar

theorem weight_log_identity (n : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t<1) :
    (∑ j ∈ Finset.range n,t^(2*(j+1))/(j+1:ℝ))+t^(2*n+2)*weight n t=
      -Real.log (1-t^2) := by
  have ht2 : |t^2|<1 := by rw [abs_of_nonneg (sq_nonneg t)]; nlinarith
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one ht2
  have he (j : ℕ) : (t^2)^(j+n+1)/(j+n+1:ℝ)=
      t^(2*n+2)*(t^(2*j)/(n+j+1:ℝ)) := by
    rw [← pow_mul,show 2*(j+n+1)=(2*n+2)+2*j by omega,pow_add]
    congr 1 <;> ring
  have hsplit := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at hsplit
  simp only [Nat.cast_add] at hsplit
  simp_rw [he] at hsplit
  rw [tsum_mul_left] at hsplit
  simpa only [weight,pow_mul] using hsplit

theorem weight_closed_form (n : ℕ) (t : ℝ) (ht : 0<t) (ht1 : t<1) :
    weight n t=(-Real.log (1-t^2)-∑ j ∈ Finset.range n,t^(2*(j+1))/(j+1:ℝ))/t^(2*n+2) := by
  have he := weight_log_identity n t ht.le ht1
  apply (eq_div_iff (pow_ne_zero _ ht.ne')).mpr
  linarith

#print axioms weight_closed_form
end BecknerOnofri.HighDim.CircleScalar
