import BecknerOnofri.CircleBesselInverse

/-! Actual circle integrals of the von Mises density equal the Bessel ratios. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleScalar

theorem vonMises_continuous (h : ℝ) : Continuous (circleTiltDensity h) := by
  unfold circleTiltDensity circleCosine
  fun_prop

theorem vonMises_moment (n : ℕ) (h : ℝ) :
    (∫ x : UnitAddCircle,circleTiltDensity h x*(fourier (n:ℤ) x).re ∂AddCircle.haarAddCircle)=
      besselMoment n h := by
  have hc := GibbsTrialLower.circleTiltFourier_eq_ratio h (-(n:ℤ))
  simp only [circleTiltFourier,neg_neg,Int.natAbs_neg,Int.natAbs_natCast] at hc
  have hi : Integrable (fun x : UnitAddCircle => fourier (n:ℤ) x*(circleTiltDensity h x:ℂ))
      AddCircle.haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (fourier (n:ℤ)).continuous.mul (Complex.continuous_ofReal.comp (vonMises_continuous h))
  have hr := congrArg Complex.re hc
  have hre : (∫ x : UnitAddCircle,fourier (n:ℤ) x*(circleTiltDensity h x:ℂ)
      ∂AddCircle.haarAddCircle).re=
      ∫ x : UnitAddCircle,(fourier (n:ℤ) x*(circleTiltDensity h x:ℂ)).re
        ∂AddCircle.haarAddCircle := (integral_re hi).symm
  rw [hre] at hr
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hr
  simpa only [mul_comm,besselMoment_eq] using hr

#print axioms vonMises_moment
end BecknerOnofri.HighDim.CircleScalar
