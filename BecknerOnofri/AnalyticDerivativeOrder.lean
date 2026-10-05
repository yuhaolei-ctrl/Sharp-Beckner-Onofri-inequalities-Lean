module

public import BecknerOnofri.AnalyticEvenOrder
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-! Differentiation lowers an actual analytic remainder's vanishing order
by one.  No differentiation rule for arbitrary big-O errors is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri

/-- For a real analytic curve into any real Banach space, an order N+1
remainder has an order N Fréchet derivative. -/
theorem analytic_fderiv_order {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F} (hf : AnalyticAt ℝ f 0) {N : ℕ}
    (ho : f =O[𝓝 0] (fun x : ℝ => ‖x‖^(N+1))) :
    fderiv ℝ f =O[𝓝 0] (fun x : ℝ => ‖x‖^N) := by
  obtain ⟨p,r,hp⟩ := hf
  have hz := coefficients_zero_of_order hp.hasFPowerSeriesAt ho
  have hd := hp.fderiv.hasFPowerSeriesAt
  have hcoeff (n : ℕ) (hn : n < N) : p.derivSeries.coeff n = 0 := by
    apply ContinuousLinearMap.ext_ring
    rw [FormalMultilinearSeries.derivSeries_coeff_one]
    change (n+1) • p (n+1) (fun _ => (1:ℝ)) = 0
    rw [hz (n+1) (by omega) 1, smul_zero]
  have hpartial : p.derivSeries.partialSum N = (fun _ => 0) := by
    funext x
    apply Finset.sum_eq_zero
    intro n hn
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff n (Finset.mem_range.mp hn), smul_zero]
  simpa only [zero_add, hpartial, sub_zero] using hd.isBigO_sub_partialSum_pow N

theorem analytic_deriv_order {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F} (hf : AnalyticAt ℝ f 0) {N : ℕ}
    (ho : f =O[𝓝 0] (fun x : ℝ => ‖x‖^(N+1))) :
    deriv f =O[𝓝 0] (fun x : ℝ => ‖x‖^N) := by
  exact ((ContinuousLinearMap.apply ℝ F (1:ℝ)).isBigO_comp _ _).trans (analytic_fderiv_order hf ho)

/-- In particular, an actual analytic quadratic expansion with a fourth-order
error can be differentiated to a linear expansion with a cubic error. -/
theorem analytic_quadratic_deriv_remainder {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (c a : ℝ) (ho : (fun t => f t - c - a*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^4)) :
    (fun t => deriv f t - 2*a*t) =O[𝓝 0] (fun t : ℝ => ‖t‖^3) := by
  have ha : AnalyticAt ℝ (fun t => f t-c-a*t^2) 0 :=
    (hf.sub analyticAt_const).sub (analyticAt_const.mul (analyticAt_id.pow 2))
  have hh := analytic_deriv_order (N := 3) ha ho
  apply hh.congr'
  · filter_upwards [hf.eventually_analyticAt] with t ht
    have he : HasDerivAt (fun y => f y-c-a*y^2) (deriv f t - 2*a*t) t := by
      convert! ((ht.differentiableAt.hasDerivAt).sub_const c).sub
        (((hasDerivAt_id t).pow 2).const_mul a) using 1
      simp only [id_eq]
      ring
    exact he.deriv
  · exact EventuallyEq.rfl

theorem analytic_quadratic_deriv_pos {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (c : ℝ) {a : ℝ} (ha : 0 < a)
    (ho : (fun t => f t-c-a*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^4)) :
    ∀ᶠ t in 𝓝 (0:ℝ), 0 < t → 0 < deriv f t := by
  have hs := (analytic_quadratic_deriv_remainder hf c a ho).trans_isLittleO
    (isLittleO_norm_pow_id (by norm_num : 1 < (3:ℕ)))
  filter_upwards [hs.bound ha] with t ht hpos
  simp only [Real.norm_eq_abs, abs_of_pos hpos] at ht
  have hlow := (abs_le.mp ht).1
  nlinarith [mul_pos ha hpos]

#print axioms analytic_deriv_order
#print axioms analytic_quadratic_deriv_remainder
end BecknerOnofri
