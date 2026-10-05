module

public import BecknerOnofri.SpinProductGibbs

@[expose] public section

/-! Analytic closure of the large-mean range. The entropy estimate applies
also at t=1 and permits zero probabilities, as required by the manuscript. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem moment_abs_le_one (s : Order) (j : Count) : |moment s j|≤1 := by
  have h : ∀ s : Order, ∀ j : Count, |momentQ s j|≤1 := by decide +kernel
  have hc := Rat.cast_le (K:=ℝ).mpr (h s j)
  simpa [moment] using hc

theorem probability_moment_abs_le_one {q : Count → ℝ}
    (hq : ∀ j,0≤q j) (hmass : (∑ j : Count,q j)=1) (s : Order) :
    |∑ j : Count,moment s j*q j|≤1 := by
  calc
    |∑ j : Count,moment s j*q j|≤∑ j : Count,|moment s j*q j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤∑ j : Count,q j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_of_nonneg (hq j)]
      simpa using mul_le_mul_of_nonneg_right (moment_abs_le_one s j) (hq j)
    _ =1 := hmass

theorem probability_quadratic_upper {q : Count → ℝ}
    (hq : ∀ j,0≤q j) (hmass : (∑ j : Count,q j)=1) :
    quadratic q≤∑ s : Order,weight s := by
  rw [quadratic_eq_sum]
  apply Finset.sum_le_sum
  intro s _
  have h := probability_moment_abs_le_one hq hmass s
  have hs : (∑ j : Count,moment s j*q j)^2≤1 := by
    have := abs_le.mp h
    nlinarith
  simpa using mul_le_mul_of_nonneg_left hs (weight_nonneg s)

theorem entropy_lower_at_smaller_mean (a t : ℝ) (q : Count → ℝ)
    (ha : 0≤a) (ha1 : a<1) (hat : a≤t) (hq : FeasibleAt t q) :
    12*binaryCost a≤relativeEntropy q reference := by
  let H : Count → ℝ := fun j => Real.log (productProbability a j/reference j)
  have hp := productProbability_pos (by linarith : -1<a) ha1
  have hpart : (∑ j : Count,reference j*Real.exp (H j))=1 := by
    have he (j : Count) : reference j*Real.exp (H j)=productProbability a j := by
      dsimp [H]
      rw [Real.exp_log (div_pos (hp j) (reference_pos j))]
      field_simp [(reference_pos j).ne']
    simp_rw [he]
    exact productProbability_mass a
  have hg := finite_gibbs_variational reference q H reference_pos hq.1.1 hq.1.2.1
  rw [hpart,Real.log_one] at hg
  have he : (∑ j : Count,q j*H j)=
      6*(Real.log (1+a)+Real.log (1-a))+
        6*(Real.log (1+a)-Real.log (1-a))*t := by
    calc
      (∑ j : Count,q j*H j)=
          6*(Real.log (1+a)+Real.log (1-a))*(∑ j : Count,q j)+
            6*(Real.log (1+a)-Real.log (1-a))*mean q := by
        simp only [H,productProbability_log_ratio (by linarith : -1<a) ha1,
          mean,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ =_ := by rw [hq.1.2.1,hq.2,mul_one]
  have hs : 0≤Real.log (1+a)-Real.log (1-a) := by
    have := Real.log_le_log (by linarith : 0<1-a) (by linarith : 1-a≤1+a)
    linarith
  rw [he] at hg
  unfold binaryCost
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hat)]

/-- The analytic large-mean lower bound in the source; a numerical lower
bound on the constructed minorant at a will later close this range. -/
theorem large_mean_spin_lower (a t : ℝ) (q : Count → ℝ) (ψ : ℝ → ℝ)
    (ha : 0≤a) (ha1 : a<1) (hat : a≤t) (hq : FeasibleAt t q)
    (hψ : ψ a≤ψ t) :
    24*binaryCost a-(∑ s : Order,weight s)+12*ψ a≤functional q+12*ψ t := by
  have he := entropy_lower_at_smaller_mean a t q ha ha1 hat hq
  have hQ := probability_quadratic_upper hq.1.1 hq.1.2.1
  unfold functional
  linarith

#print axioms entropy_lower_at_smaller_mean
#print axioms large_mean_spin_lower
end BecknerOnofri.HighDim.Spin
