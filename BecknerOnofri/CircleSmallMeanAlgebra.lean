module

public import BecknerOnofri.CircleScalarCandidates
public import BecknerOnofri.SpinBinaryCostUpper

@[expose] public section

/-! The exact square completion and small-mean margin used in the source's
γ estimate. The analytic rate-function and weight bounds remain separate
proof obligations; they are explicit hypotheses of this intermediate lemma. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem source_quadratic_lower (t x : ℝ) :
    (5697/34880:ℝ)*t^4≤(633/2000)*x^2+(27/80)*(x-t^2)^2 := by
  nlinarith [sq_nonneg (x-(225/436:ℝ)*t^2)]

theorem small_mean_cost_lower (t I B C D L x : ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hI : t^2+t^4/4≤I)
    (hB : (27/80:ℝ)≤B) (hC : 0≤C) :
    (3/40:ℝ)*t^4≤(13/40)*I+(27/40)*t^2-2*Spin.binaryCost t+
      cost (633/2000) B C D L (t^2) x := by
  have hu := Spin.binaryCost_quartic_upper ht (by linarith : t<1)
  have ht2 : t^2≤(1/256:ℝ) := by nlinarith
  have hd : 0<1-t^2 := by linarith
  have hr : 1/(6*(1-t^2))≤(128/765:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0<6*(1-t^2))).mpr
    linarith
  have hf := mul_le_mul_of_nonneg_left hr (pow_nonneg ht 4)
  have hbin : 2*Spin.binaryCost t≤t^2+(128/765)*t^4 := by
    have he : t^4/(6*(1-t^2))=t^4*(1/(6*(1-t^2))) := by ring
    rw [he] at hu
    linarith
  have hs := source_quadratic_lower t x
  have hsq := mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg (x-t^2))
  have hc := mul_nonneg hC (sq_nonneg (max 0 (L-D*x)))
  have hi := mul_le_mul_of_nonneg_left hI (by norm_num : (0:ℝ)≤13/40)
  have hm : (3/40:ℝ)≤13/160+5697/34880-128/765 := by norm_num
  have htm := mul_le_mul_of_nonneg_right hm (pow_nonneg ht 4)
  unfold cost
  nlinarith

theorem small_mean_candidate_lower (t I B C D L m : ℝ)
    (ht : 0≤t) (ht1 : t≤1/16) (hI : t^2+t^4/4≤I)
    (hB : (27/80:ℝ)≤B) (hC : 0≤C) :
    (3/40:ℝ)*t^4≤(13/40)*I+(27/40)*t^2-2*Spin.binaryCost t+
      candidateMinimum (633/2000) B C D L (t^2) m := by
  obtain ⟨x,_,hx⟩ := candidateMinimum_attained (633/2000) B C D L (t^2) m
  rw [← hx]
  exact small_mean_cost_lower t I B C D L x ht ht1 hI hB hC

#print axioms small_mean_candidate_lower
end BecknerOnofri.HighDim.CircleScalar
