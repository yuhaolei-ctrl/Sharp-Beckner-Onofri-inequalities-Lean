import BecknerOnofri.GreenCoordinateComparison
import Legacy.BecknerOnofri.GreenHeatIntegrability

/-! The coordinate comparison on the Haar torus. All exceptional coordinate
hyperplanes are removed by their proved zero measure. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
open scoped BigOperators
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri.GreenHeatPointwise Legacy.BecknerOnofri.TorusLogIntegrability

theorem ae_of_cell_except_coordinate_zeros {d : ℕ} {p : Torus d → Prop}
    (hp : MeasurableSet {z | p z})
    (h : ∀ x ∈ centeredCell d, (∀ i, x i ≠ 0) → p (quotientPoint x)) :
    ∀ᵐ z ∂torusMeasure d, p z := by
  rw [← (quotientPoint_measurePreserving d).map_eq]
  apply (ae_map_iff (quotientPoint_measurePreserving d).aemeasurable hp).2
  have hz : ∀ᵐ x : Fin d → ℝ ∂volume, ∀ i, x i ≠ 0 := by
    apply ae_all_iff.2
    intro i
    exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i 0
  filter_upwards [ae_restrict_mem (centeredCell_measurable d), ae_restrict_of_ae hz] with x hx hzero
  exact h x hx hzero

theorem heatGreen_average_coordinates_ae {d : ℕ} (hd : 0 < d) :
    ∀ᵐ x : Torus d ∂torusMeasure d, heatGreen x ≤
      (∑ i, heatGreen (fun _ : Fin 1 => x i)) / (d : ℝ) +
        coordinateComparisonConstant d := by
  apply ae_of_cell_except_coordinate_zeros
  · apply measurableSet_le (measurable_heatGreen d)
    exact ((Finset.measurable_sum _ (fun i _ =>
      (measurable_heatGreen 1).comp (measurable_pi_lambda _ (fun _ => measurable_pi_apply i)))).div_const _).add_const _
  · intro x hx hzero
    exact heatGreen_average_coordinates_le hd x (centeredCell_coordinates hx) hzero

#print axioms heatGreen_average_coordinates_ae
end BecknerOnofri.AdamsEndpoint
