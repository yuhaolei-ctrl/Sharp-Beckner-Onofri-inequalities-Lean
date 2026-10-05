module

public import Legacy.BecknerOnofri.GreenHeatMeasurable
public import Legacy.BecknerOnofri.TorusLogIntegrability

@[expose] public section

/-! Exponential moments and L2 membership of the actual heat-Mellin kernel.
Identification with the Fourier-constructed Green kernel is kept separate.
-/
namespace Legacy.BecknerOnofri.GreenHeatPointwise
open MeasureTheory Legacy.TorusEndpoint TorusLogIntegrability

theorem heatGreen_exp_integrable {d : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 ≤ a) (had : a < d) :
    Integrable (fun x : Torus d => Real.exp (a * heatGreen x)) (torusMeasure d) := by
  apply exp_integrable_of_log_radius_bound (C := upperConstant d) hd ha had heatGreen
    (measurable_heatGreen d).aestronglyMeasurable
  intro x hx hx0
  exact heatGreen_le_log hd x (centeredCell_coordinates hx) hx0

theorem heatGreen_lower_ae {d : ℕ} (hd : 0 < d) :
    ∀ᵐ x : Torus d ∂torusMeasure d, -lowerConstant d ≤ heatGreen x := by
  apply ae_of_cell_except_zero hd
    (measurableSet_le measurable_const (measurable_heatGreen d))
  intro x hx hx0
  exact heatGreen_lower hd x (centeredCell_coordinates hx) hx0

theorem heatGreen_memLp {d : ℕ} (hd : 0 < d) :
    MemLp (@heatGreen d) 2 (torusMeasure d) := by
  have hdreal : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply memLp_two_of_lower_and_exp_integrable heatGreen
    (measurable_heatGreen d).aestronglyMeasurable (a := (d : ℝ)/2) (by positivity)
    (heatGreen_lower_ae hd)
  exact heatGreen_exp_integrable hd (by positivity) (by linarith)

#print axioms heatGreen_exp_integrable
#print axioms heatGreen_memLp
end Legacy.BecknerOnofri.GreenHeatPointwise
