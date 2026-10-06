module

public import BecknerOnofri.AnalyticEvenSquare
public import BecknerOnofri.AnalyticParameterOrderDivision
public import Mathlib.Analysis.Calculus.DSlope

@[expose] public section

/-! The linear coefficient after replacing an even analytic amplitude by its
square is determined by the actual quadratic expansion, not postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticEvenSquare

theorem square_factor_derivative {f g : ℝ → ℝ} {c : ℝ}
    (hg : AnalyticAt ℝ g 0) (he : ∀ᶠ t in 𝓝 (0:ℝ),f t=g (t^2))
    (ho : (fun t : ℝ => f t-f 0-c*t^2) =O[𝓝 0] (fun t => ‖t‖^3)) :
    HasDerivAt g c 0 := by
  have h0 : f 0=g 0 := by simpa only [zero_pow (by decide : 2≠0)] using he.self_of_nhds
  have hc : ContinuousAt (fun t : ℝ => dslope g 0 (t^2)) 0 := by
    have hg' : ContinuousAt (dslope g 0) (0:ℝ) :=
      continuousAt_dslope_same.mpr hg.differentiableAt
    have hs : ContinuousAt (fun t : ℝ => t^2) 0 := continuousAt_id.pow 2
    have hg'' : ContinuousAt (dslope g 0) ((0:ℝ)^2) := by simpa using hg'
    exact hg''.comp (f := fun t : ℝ => t^2) hs
  have heq : ∀ᶠ t in 𝓝 (0:ℝ),f t-f 0=t^2*dslope g 0 (t^2) := by
    filter_upwards [he] with t ht
    rw [ht,h0]
    simpa only [sub_zero,smul_eq_mul] using (sub_smul_dslope g 0 (t^2)).symm
  have ho' : (fun t : ℝ => (f t-f 0)-t^2*c) =O[𝓝 0] (fun t => ‖t‖^(2+1)) := by
    simpa only [mul_comm c] using ho
  have hd := AnalyticParameterDivision.power_factor_value hc heq ho'
  have hd' : deriv g 0=c := by simpa only [zero_pow (by decide : 2≠0),dslope_same] using hd
  simpa only [hd'] using hg.differentiableAt.hasDerivAt

/-- The square variable has a genuine analytic germ on both sides of zero. -/
theorem exists_square_parameter {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f 0) (he : ∀ᶠ t in 𝓝 (0:ℝ),f (-t)=f t)
    (ho : (fun t : ℝ => f t-f 0-c*t^2) =O[𝓝 0] (fun t => ‖t‖^3)) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ g 0=f 0 ∧ HasDerivAt g c 0 ∧
      ∀ᶠ t in 𝓝 (0:ℝ),f t=g (t^2) := by
  obtain ⟨g,hg,heq⟩ := exists_analytic_square_factor hf he
  refine ⟨g,hg,?_,square_factor_derivative hg heq ho,heq⟩
  simpa only [zero_pow (by decide : 2≠0)] using heq.self_of_nhds.symm

#print axioms exists_square_parameter
end BecknerOnofri.AnalyticEvenSquare
