module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import BecknerOnofri.AnalyticSquareParameter
public import BecknerOnofri.AnalyticScalarInverse
public import BecknerOnofri.AnalyticScalarTaylor
public import BecknerOnofri.AnalyticPitchfork

@[expose] public section

/-! Analytic squared-amplitude parametrization for an actual odd scalar residual
whose analytic data have been supplied, with the manuscript's parameter delta=1-1/tau. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.AnalyticPitchfork

theorem exists_squared_parameter (D : Data) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ g 0=1 ∧ HasDerivAt g (D.coefficient) 0 ∧
      ∀ᶠ t in 𝓝 (0:ℝ), parameter D t=g (t^2) := by
  have ho : (fun t => parameter D t-parameter D 0-D.coefficient*t^2)
      =O[𝓝 (0:ℝ)] (fun t => ‖t‖^3) := by
    simpa only [parameter_base] using (parameter_expansion D).trans
      (norm_pow_bigO_of_le (by norm_num : 3≤4))
  simpa only [parameter_base] using AnalyticEvenSquare.exists_square_parameter
    (parameter_analytic D) (parameter_even D) ho

/-- Genuine analytic squared amplitudes, rather than only a square-root asymptotic. -/
theorem exists_analytic_squared_amplitude (D : Data) (hD : 0<D.coefficient) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r 0 ∧ r 0=0 ∧ HasDerivAt r (D.coefficient)⁻¹ 0 ∧
      ((fun δ => r δ-δ/D.coefficient) =O[𝓝 (0:ℝ)] (fun δ => ‖δ‖^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ), r (1-1/parameter D t)=t^2) := by
  obtain ⟨g,hg,hg0,hgd,he⟩ := exists_squared_parameter D
  let H : ℝ → ℝ := fun s => 1-1/g s
  have hH : AnalyticAt ℝ H 0 :=
    analyticAt_const.sub (analyticAt_const.div hg (by rw [hg0]; norm_num))
  have hH0 : H 0=0 := by first | rfl | simp [H,hg0]
  have hHd : HasDerivAt H (D.coefficient) 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:ℝ)).sub
      ((hasDerivAt_const (0:ℝ) (1:ℝ)).div hgd (by rw [hg0]; norm_num)) using 1 <;>
      first | rfl | simp [H,hg0]
  obtain ⟨r,hr,hr0,hrd,hl,hright⟩ := exists_analytic_scalar_inverse hH hH0 hHd
    hD.ne'
  refine ⟨r,hr,hr0,hrd,?_,?_⟩
  · simpa only [hr0,sub_zero,div_eq_mul_inv,mul_comm] using analytic_linear_remainder hr hrd
  · have ht : Tendsto (fun t : ℝ => t^2) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => t^2) := continuous_id.pow 2
      simpa using hc.continuousAt.tendsto (x := (0:ℝ))
    filter_upwards [he,ht.eventually hl] with t he hl
    simpa only [H,← he] using hl

#print axioms exists_analytic_squared_amplitude
end BecknerOnofri.AnalyticPitchfork
