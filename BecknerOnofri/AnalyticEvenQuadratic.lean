module

public import BecknerOnofri.AnalyticScalarTaylor
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

theorem analytic_even_derivative_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (he : ∀ᶠ t in 𝓝 (0:ℝ),f (-t)=f t) : HasDerivAt f 0 0 := by
  have hp := hf.differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun t : ℝ => f (-t)) (-deriv f 0) 0 := by
    have hpn : HasDerivAt f (deriv f 0) (-(0:ℝ)) := by simpa using hp
    convert hpn.comp 0 (hasDerivAt_neg (0:ℝ)) using 1 <;> first | rfl | simp
  have heq := hp.unique (hn.congr_of_eventuallyEq (he.mono (fun _ h => h.symm)))
  have hz : deriv f 0=0 := by linarith
  simpa only [hz] using hp

theorem analytic_even_quadratic_remainder {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (he : ∀ᶠ t in 𝓝 (0:ℝ),f (-t)=f t) :
    (fun t => f t-f 0) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2) := by
  simpa only [zero_mul,sub_zero] using
    analytic_linear_remainder hf (analytic_even_derivative_zero hf he)

#print axioms analytic_even_quadratic_remainder
end BecknerOnofri
