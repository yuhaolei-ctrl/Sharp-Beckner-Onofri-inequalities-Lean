import BecknerOnofri.CircleGammaActual

/-! The quantitative gamma bound for an actual normalized circle density
with an increasing convex logarithmic cosine profile. Both the entropy
remainder and moment comparisons are discharged by their proved theorems. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.CirclePoisson
open CircleScalar

theorem gamma_entropy_of_convex_profile (p : Torus 1 → ℝ) (hp : Continuous p)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hsmooth : ContDiff ℝ 3 (fun x : ℝ => p (fun _ => (x:UnitAddCircle))))
    (F : ℝ → ℝ) (hcF : ContinuousOn F (Icc (-1:ℝ) 1))
    (hF : ConvexOn ℝ (Icc (-1:ℝ) 1) F) (hinc : MonotoneOn F (Icc (-1:ℝ) 1))
    (hprofile : ∀ x,p x=Real.exp (F ((fourier 1 (x 0)).re))) :
    2*Spin.binaryCost (moment p 1)+gamma (moment p 1)+(21/1000)*(moment p 2)^2+
      (27/40)*(∑' n : ℕ,(moment p (n+3))^2/(n+3:ℝ)) ≤
        ∫ x,p x*Real.log (p x) ∂torusMeasure 1 := by
  have hpos (x : Torus 1) : 0<p x := by rw [hprofile]; exact Real.exp_pos _
  have hcos (z : UnitAddCircle) : (fourier 1 (-z)).re=(fourier 1 z).re := by
    simp only [fourier_apply,zsmul_neg,AddCircle.toCircle_neg]
    simp
  have he (x : Torus 1) : p (-x)=p x := by
    rw [hprofile,hprofile]
    simp only [Pi.neg_apply,hcos]
  have hmass : (∫ z : UnitAddCircle,Real.exp (F ((fourier 1 z).re)) ∂AddCircle.haarAddCircle)=1 := by
    simpa only [hprofile] using (integral_torus_circle p).symm.trans hm
  have hmean : (∫ z : UnitAddCircle,Real.exp (F ((fourier 1 z).re))*(fourier 1 z).re
      ∂AddCircle.haarAddCircle)=moment p 1 := by
    simpa only [hprofile,Nat.cast_one] using (moment_eq_cosine_integral p hp 1).symm
  obtain ⟨ht,_,ha,hb,hI⟩ := circle_comparison_on F (moment p 1) hcF hF hinc hmass hmean
  have h2 := moment_eq_cosine_integral p hp 2
  have h3 := moment_eq_cosine_integral p hp 3
  simp only [hprofile,Nat.cast_ofNat] at h2 h3
  rw [← h2] at ha
  rw [← h2,← h3] at hb
  have hEnt := integral_torus_circle (fun x => p x*Real.log (p x))
  simp only [hprofile] at hEnt
  rw [← hEnt] at hI
  apply gamma_of_comparisons p hp hpos he hm hsmooth ht _ ha hb
  simpa only [hprofile] using hI

#print axioms gamma_entropy_of_convex_profile
end BecknerOnofri.HighDim.CirclePoisson
