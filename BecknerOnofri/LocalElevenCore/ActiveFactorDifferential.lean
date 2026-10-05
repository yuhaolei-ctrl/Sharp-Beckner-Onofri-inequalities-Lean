import BecknerOnofri.LocalElevenCore.ActiveFactorNonzero

/-! Differentiating the actual analytic squared-amplitude divisibility identity.
This is the transverse part of the active-amplitude Hessian calculation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor

/-- On the equal-amplitude locus, the derivative of the difference of the
actual coordinate factors is exactly the squared-amplitude difference
functional times the analytic quotient. -/
theorem differential_squared_difference {d : ℕ} (hd : 11≤d) (i j : Fin d)
    {H : Input d → ℝ} (hH : AnalyticAt ℝ H (1,0))
    (he : ∀ᶠ x : Input d in 𝓝 (1,0),
      factor hd i x-factor hd j x=(x.2 i^2-x.2 j^2)*H x) :
    ∀ᶠ x : Input d in 𝓝 (1,0), x.2 i=x.2 j → ∀ h : Input d,
      fderiv ℝ (factor hd i) x h-fderiv ℝ (factor hd j) x h =
        2*x.2 i*(h.2 i-h.2 j)*H x := by
  filter_upwards [he.eventually_nhds,hH.eventually_analyticAt,
    (factor_analytic hd i).eventually_analyticAt,
    (factor_analytic hd j).eventually_analyticAt] with x hx hHx hi hj heq h
  have hq := (((coordinate d i).hasFDerivAt (x := x)).pow 2).sub
    (((coordinate d j).hasFDerivAt (x := x)).pow 2)
  have hr := (hq.mul hHx.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hx
  have hl := hi.differentiableAt.hasFDerivAt.sub hj.differentiableAt.hasFDerivAt
  have hv := congrArg (fun L : Input d →L[ℝ] ℝ => L h) (hl.unique hr)
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,coordinate_apply,Pi.sub_apply] at hv
  rw [← heq] at hv
  norm_num at hv
  nlinarith [hv]

#print axioms differential_squared_difference
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
