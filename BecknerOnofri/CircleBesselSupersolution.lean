import BecknerOnofri.CircleBesselRiccati
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The explicit supersolution in the source's Riccati comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.CircleScalar

def riccatiSupersolution (h : ℝ) : ℝ := h/Real.sqrt (1+h^2)
def riccatiSupersolutionSlope (h : ℝ) : ℝ := 1/(Real.sqrt (1+h^2))^3

theorem besselMoment_one_zero : besselMoment 1 0=0 := by
  simp [besselMoment,bessel,pow_add]

theorem besselMoment_nonneg (n : ℕ) {h : ℝ} (hh : 0≤h) : 0≤besselMoment n h := by
  unfold besselMoment bessel
  apply div_nonneg <;> apply tsum_nonneg <;> intro j <;> positivity

theorem besselMoment_first_derivative (h : ℝ) :
    HasDerivAt (besselMoment 1) (1+besselMoment 2 h-2*(besselMoment 1 h)^2) h := by
  have hd := besselMoment_derivative 1 (by decide) h
  have hz : besselMoment 0 h=1 := by
    rw [besselMoment_eq]
    exact GibbsTrialLower.besselRatio_zero h
  norm_num only [Nat.sub_self,Nat.reduceAdd,hz] at hd
  convert hd using 1 <;> ring

theorem riccatiSupersolution_derivative (h : ℝ) :
    HasDerivAt riccatiSupersolution (riccatiSupersolutionSlope h) h := by
  have hp : 0<1+h^2 := by positivity
  have hr : 0<Real.sqrt (1+h^2) := Real.sqrt_pos.mpr hp
  have hs := Real.sq_sqrt hp.le
  have hd := (hasDerivAt_id h).div
    ((Real.hasDerivAt_sqrt hp.ne').comp h (((hasDerivAt_id h).pow 2).const_add 1)) hr.ne'
  convert hd using 1 <;> try rfl
  dsimp [riccatiSupersolutionSlope]
  field_simp [hr.ne']
  nlinarith

theorem riccatiSupersolution_weighted_residual (h : ℝ) :
    riccatiSupersolution h+h*riccatiSupersolutionSlope h+
      2*h*(riccatiSupersolution h)^2-2*h=
      h*(Real.sqrt (1+h^2)-1)^2/(Real.sqrt (1+h^2))^3 := by
  have hp : 0<1+h^2 := by positivity
  have hr : 0<Real.sqrt (1+h^2) := Real.sqrt_pos.mpr hp
  have hs := Real.sq_sqrt hp.le
  unfold riccatiSupersolution riccatiSupersolutionSlope
  field_simp [hr.ne']
  nlinarith [congrArg (fun x : ℝ => h*x) hs]

#print axioms riccatiSupersolution_derivative
#print axioms riccatiSupersolution_weighted_residual
end BecknerOnofri.HighDim.CircleScalar
