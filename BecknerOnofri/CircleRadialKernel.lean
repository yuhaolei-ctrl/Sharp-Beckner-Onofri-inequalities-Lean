import BecknerOnofri.PolarizationMetricGeometry
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of an even decreasing circle kernel is a consequence of
its radial monotonicity, not an extra premise on the manuscript's kernel. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1

theorem circle_radial_kernel_measurable {q : UnitAddCircle → ℝ}
    (hq : ∀ x y,‖x‖≤‖y‖ → q y≤q x) : Measurable q := by
  let r : ℝ → ℝ := fun t => min (1/2) (max 0 t)
  have hr0 (t : ℝ) : 0≤r t := le_min (by norm_num) (le_max_left _ _)
  have hr1 (t : ℝ) : r t≤1/2 := min_le_left _ _
  have hr : Monotone r := monotone_const.min (monotone_const.max monotone_id)
  have hn (t : ℝ) : ‖(r t : UnitAddCircle)‖=r t := by
    rw [circle_norm_small (by rw [abs_of_nonneg (hr0 t)]; exact hr1 t),abs_of_nonneg (hr0 t)]
  have hφ : Antitone (fun t : ℝ => q (r t : UnitAddCircle)) := by
    intro s t hst
    apply hq
    simpa only [hn] using hr hst
  have he : q=(fun t : ℝ => q (r t : UnitAddCircle)) ∘ (fun x : UnitAddCircle => ‖x‖) := by
    funext x
    have hrx : r ‖x‖=‖x‖ := by
      dsimp [r]
      rw [max_eq_right (norm_nonneg x),min_eq_right]
      simpa using AddCircle.norm_le_half_period 1 (x := x) (by norm_num)
    have hnorm : ‖(r ‖x‖ : UnitAddCircle)‖=‖x‖ := (hn _).trans hrx
    exact le_antisymm (hq _ _ hnorm.le) (hq _ _ hnorm.ge)
  rw [he]
  exact hφ.measurable.comp continuous_norm.measurable

#print axioms circle_radial_kernel_measurable
end BecknerOnofri.PolarizationL1
