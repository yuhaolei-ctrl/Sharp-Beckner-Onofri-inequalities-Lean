module

public import BecknerOnofri.SpinFiniteGibbs
public import BecknerOnofri.CenteredExponential

@[expose] public section

/-! The centered exponential-moment bound used in the small-mean range,
with its exact rational denominator rather than a floating-point estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem exp_le_reciprocal {x : ℝ} (hx : x<1) : Real.exp x≤1/(1-x) := by
  have h := Real.add_one_le_exp (-x)
  rw [Real.exp_neg] at h
  have hh : (1-x)*Real.exp x≤1 := by
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos x).le
    rw [inv_mul_cancel₀ (Real.exp_ne_zero x)] at h'
    linarith
  exact (le_div_iff₀ (sub_pos.mpr hx)).mpr (by nlinarith)

theorem finite_centered_log_mgf (p H : Count → ℝ) (B : ℝ)
    (hp : ∀ j,0<p j) (hmass : (∑ j : Count,p j)=1)
    (hcenter : (∑ j : Count,p j*H j)=0)
    (hB : 0≤B) (hsmall : 5*B<1) (hbound : ∀ j,|H j|≤B) :
    (1/5)*Real.log (∑ j : Count,p j*Real.exp (5*H j)) ≤
      ((5/2)/(1-5*B))*(∑ j : Count,p j*(H j)^2) := by
  let V := ∑ j : Count,p j*(H j)^2
  have hV : 0≤V := Finset.sum_nonneg (fun j _ => mul_nonneg (hp j).le (sq_nonneg _))
  have hj (j : Count) : p j*Real.exp (5*H j)≤
      p j+5*(p j*H j)+(25/2)*Real.exp (5*B)*(p j*(H j)^2) := by
    have ha : |5*H j|≤5*B := by
      rw [abs_mul]
      norm_num
      linarith [hbound j]
    have h := BecknerOnofri.HighDim.exp_le_quadratic_of_abs_le (by positivity) ha
    have hh := mul_le_mul_of_nonneg_left h (hp j).le
    nlinarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Count)) => hj j)
  have hZ : (∑ j : Count,p j*Real.exp (5*H j))≤1+(25/2)*Real.exp (5*B)*V := by
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum,hmass,hcenter,mul_zero,add_zero,V] using hsum
  have hlog := Real.log_le_sub_one_of_pos (finite_partition_pos p (fun j => 5*H j) hp)
  have hexp := mul_le_mul_of_nonneg_right (exp_le_reciprocal hsmall) hV
  change (1/5)*Real.log (∑ j : Count,p j*Real.exp (5*H j))≤((5/2)/(1-5*B))*V
  have he : ((5/2)/(1-5*B))*V=(5/2)*(1/(1-5*B)*V) := by ring
  rw [he]
  linarith

#print axioms finite_centered_log_mgf
end BecknerOnofri.HighDim.Spin
