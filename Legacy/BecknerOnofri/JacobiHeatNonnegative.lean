import Legacy.BecknerOnofri.JacobiHeatKernelAction
import Legacy.BecknerOnofri.AngularPolynomialPositivity

/-! Nonnegativity of the actual Jacobi heat kernel, proved from actual parabolic comparison
and positive polynomial approximation, without a semigroup-positivity premise. -/
noncomputable section
open Set MeasureTheory Filter Polynomial Classical
open scoped Topology ContDiff
namespace Legacy.BecknerOnofri.JacobiHeatPositivity
open JacobiEigenfunctions JacobiHeatBounds

/-- The complete actual Jacobi heat kernel is nonnegative on the open Dirichlet interval. -/
theorem heatKernel_nonnegative_interior {m : ℕ} (hm : 0<m) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Icc 0 Real.pi) (hy : y∈Ioo 0 Real.pi) :
    0≤heatKernel m t x y := by
  apply nonnegative_of_angularPolynomial_tests m (heatKernel_continuous_right m ht x) _ hy
  intro p hp
  rw [heatKernel_polynomial m hm p ht x]
  exact polynomialHeat_nonnegative hm p hp ht.le hx

/-- The positivity extends to the closed interval using the proved spectral zero boundary. -/
theorem heatKernel_nonnegative {m : ℕ} (hm : 0<m) {t x y : ℝ}
    (ht : 0<t) (hx : x∈Icc 0 Real.pi) (hy : y∈Icc 0 Real.pi) :
    0≤heatKernel m t x y := by
  by_cases hy0 : y=0
  · subst y
    simp [heatKernel,normalizedFunction_zero hm]
  by_cases hyπ : y=Real.pi
  · subst y
    simp [heatKernel,normalizedFunction_pi hm]
  exact heatKernel_nonnegative_interior hm ht hx
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),lt_of_le_of_ne hy.2 hyπ⟩

theorem heatKernel_mul_integrable (m : ℕ) {t : ℝ} (ht : 0<t) (x : ℝ)
    {g : ℝ→ℝ} (hg : Integrable g intervalMeasure) :
    Integrable (fun y => heatKernel m t x y*g y) intervalMeasure := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s:=Icc 0 Real.pi) (heatKernel_continuous_right m ht x).continuousOn
  apply hg.bdd_mul (heatKernel_continuous_right m ht x).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact hC y ⟨hy.1.le,hy.2.le⟩

/-- The actual kernel integral of every integrable nonnegative initial function is nonnegative. -/
theorem heatKernel_action_nonnegative {m : ℕ} (hm : 0<m) {t x : ℝ}
    (ht : 0<t) (hx : x∈Icc 0 Real.pi) {g : ℝ→ℝ}
    (hg : Integrable g intervalMeasure) (hgn : ∀ᵐy∂intervalMeasure,0≤g y) :
    Integrable (fun y => heatKernel m t x y*g y) intervalMeasure ∧
      0≤∫y,heatKernel m t x y*g y ∂intervalMeasure := by
  refine ⟨heatKernel_mul_integrable m ht x hg,integral_nonneg_of_ae ?_⟩
  filter_upwards [hgn,ae_restrict_mem measurableSet_Ioo] with y hy hyi
  exact mul_nonneg (heatKernel_nonnegative_interior hm ht hx hyi) hy

#print axioms heatKernel_nonnegative
#print axioms heatKernel_action_nonnegative
end Legacy.BecknerOnofri.JacobiHeatPositivity
