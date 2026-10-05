module

public import BecknerOnofri.SpinSegmentBounds
public import BecknerOnofri.SpinDifferentialDefinitions

@[expose] public section

/-! Global supporting parabolas on every mean slice, with the exact
constants of the 2026-09-21 manuscript and boundary probabilities allowed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem matrix_gradient_pairing (p v : Count → ℝ) :
    (∑ j : Count,(∑ k : Count,interaction j k*p k)*v j)=bilinear p v := by
  simp only [bilinear,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [interaction_symmetric j k]
  ring

theorem slope_at_zero_eq_gradient (p v : Count → ℝ) (hp : ∀ j,0<p j) :
    functionalSlope p v 0=∑ j : Count,gradient p j*v j := by
  have he (j : Count) :
      gradient p j*v j=2*((Real.log (p j)-Real.log (reference j)+1)*v j)-
        2*((∑ k : Count,interaction j k*p k)*v j) := by
    rw [gradient,Real.log_div (hp j).ne' (reference_pos j).ne']
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,matrix_gradient_pairing]
  simp [functionalSlope,entropySlope]

theorem gradient_residual_pairing {p v : Count → ℝ} {δ ell η : ℝ}
    (hδ : ∀ j,|gradient p j-ell-η*meanCoordinate j|≤δ)
    (hmass : (∑ j : Count,v j)=0) :
    η*mean v-δ*l1 v≤∑ j : Count,gradient p j*v j := by
  have hpoint (j : Count) :
      ell*v j+η*(meanCoordinate j*v j)-δ*|v j|≤gradient p j*v j := by
    have h1 := mul_le_mul_of_nonneg_right (hδ j) (abs_nonneg (v j))
    have h2 := neg_abs_le ((gradient p j-ell-η*meanCoordinate j)*v j)
    rw [abs_mul] at h2
    nlinarith
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset Count)) => hpoint j)
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hmass,
    mul_zero,zero_add,mean,l1] using h

/-- Corollary 5.19: a rational approximate stationary point gives a global
lower parabola for every feasible vector, without an optimality hypothesis. -/
theorem global_supporting_parabola (p q : Count → ℝ) (s t δ ell η : ℝ)
    (hp : FeasibleAt s p) (hpos : ∀ j,0<p j) (hq : FeasibleAt t q)
    (hδ : ∀ j,|gradient p j-ell-η*meanCoordinate j|≤δ) :
    functional p+η*(t-s)-350*(t-s)^2-5*δ^2≤functional q := by
  have hv : (∑ j : Count,(q-p) j)=0 := by
    simp [Finset.sum_sub_distrib,hp.1.2.1,hq.1.2.1]
  have hg := gradient_residual_pairing (v:=q-p) hδ hv
  rw [← slope_at_zero_eq_gradient p (q-p) hpos,mean_sub,hq.2,hp.2] at hg
  have hr := functional_support_remainder hp.1 hpos hq.1
  rw [hq.2,hp.2] at hr
  nlinarith [sq_nonneg (l1 (q-p)-10*δ)]

#print axioms global_supporting_parabola
end BecknerOnofri.HighDim.Spin
