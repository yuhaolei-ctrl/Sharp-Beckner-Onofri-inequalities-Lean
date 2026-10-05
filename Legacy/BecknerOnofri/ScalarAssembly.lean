import Legacy.BecknerOnofri.FiniteScalar
import Legacy.BecknerOnofri.UniformTail
import Legacy.BecknerOnofri.ThetaIntegrability
import Legacy.BecknerOnofri.EulerLower
import Legacy.BecknerOnofri.ThetaIntegralBound

/-!
Assembly of the finite certificate and the common tail. The numerical bound
on the actual theta integral is proved in `ThetaIntegralBound`. The remaining
Gaussian-tail estimate is an explicit mathematical hypothesis, not an axiom.
-/
namespace Legacy.BecknerOnofri
open UniformTail ThetaDomination

noncomputable def scalarGap (d n : ℕ) : ℝ :=
  (d : ℝ) * (Legacy.D10.FiniteScalar.harmonic n : ℝ) -
    (2 * endpointConstant d) * FiniteScalar.polynomialEnergy d n

noncomputable def scalarDelta (d : ℕ) : ℝ :=
  delta d Real.eulerMascheroniConstant (Real.log Real.pi) (Real.log 2)
    (thetaIntegral realTheta d)

/-- The numerical theta statement concerns the actual improper integral. -/
def ThetaIntegralBound : Prop := thetaIntegral realTheta 10 < 41/25

/-- The former numerical theta obligation is now discharged. -/
theorem thetaIntegralBound : ThetaIntegralBound := ThetaBound.realThetaIntegral_ten_lt

/-- The manuscript's eight dimension-uniform Delta margins, with all
numerical and theta-integral inputs proved. -/
theorem scalarDelta_gt_common {d : ℕ} (hd : 3 ≤ d) (hd10 : d ≤ 10) :
    (3/200 : ℝ) * tailWeight d < scalarDelta d := by
  exact delta_gt_common d hd hd10 Real.eulerMascheroniConstant
    (Real.log Real.pi) (Real.log 2) (thetaIntegral realTheta d)
    EulerLower.gamma_lower log_pi_upper log_two_upper
    (ThetaBound.realThetaIntegral_lt (by omega) hd10).le

/-- The remaining Mellin/Jacobi/Gaussian analysis must establish this estimate.
The statement is a target definition, not a claimed theorem. -/
def GaussianTailBound (d : ℕ) : Prop :=
  ∀ n : ℕ, 22 ≤ n →
    scalarDelta d - tailWeight d / Real.pi * Real.log (1+1/(n : ℝ)) ≤ scalarGap d n

 theorem large_scalar_gap_of_bounds {d n : ℕ}
    (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 22 ≤ n)
    (hJ : ThetaIntegralBound) (hGaussian : GaussianTailBound d) :
    (3/1100 : ℝ) < scalarGap d n := by
  exact uniform_large_gap_of_real_constants d n hd hd10 hn
    Real.eulerMascheroniConstant (thetaIntegral realTheta d)
    (thetaIntegral realTheta 10) (scalarGap d n) EulerLower.gamma_lower
    (realThetaIntegral_le_tenth_unconditional hd10) hJ (hGaussian n hn)

/-- The original conditional interface, retaining the theta argument for
compatibility. `thetaIntegralBound` now supplies that argument unconditionally;
the Gaussian-tail premise still needs proof. -/
theorem all_indices_scalar_gap_of_bounds {d n : ℕ}
    (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n)
    (hJ : ThetaIntegralBound) (hGaussian : GaussianTailBound d) :
    (3/1100 : ℝ) < scalarGap d n := by
  by_cases hsmall : n ≤ 21
  · exact FiniteScalar.finite_polynomial_gap hd hd10 hn hsmall
  · exact large_scalar_gap_of_bounds hd hd10 (by omega) hJ hGaussian

/-- Only the Mellin/Jacobi/Gaussian estimate remains as an analytic premise. -/
theorem large_scalar_gap_of_gaussian {d n : ℕ}
    (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 22 ≤ n)
    (hGaussian : GaussianTailBound d) : (3/1100 : ℝ) < scalarGap d n :=
  large_scalar_gap_of_bounds hd hd10 hn thetaIntegralBound hGaussian

/-- The complete finite-certificate range and the common tail are assembled
without any unproved theta-integral bound. This is still a conditional scalar
theorem, not an endpoint inequality for arbitrary probability densities. -/
theorem all_indices_scalar_gap_of_gaussian {d n : ℕ}
    (hd : 3 ≤ d) (hd10 : d ≤ 10) (hn : 1 ≤ n)
    (hGaussian : GaussianTailBound d) : (3/1100 : ℝ) < scalarGap d n :=
  all_indices_scalar_gap_of_bounds hd hd10 hn thetaIntegralBound hGaussian

#print axioms all_indices_scalar_gap_of_bounds
#print axioms thetaIntegralBound
#print axioms scalarDelta_gt_common
#print axioms all_indices_scalar_gap_of_gaussian
end Legacy.BecknerOnofri
