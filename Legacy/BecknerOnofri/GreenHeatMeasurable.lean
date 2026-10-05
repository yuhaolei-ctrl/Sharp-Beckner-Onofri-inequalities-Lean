module

public import Legacy.BecknerOnofri.GreenHeatPointwise

@[expose] public section

/-! Joint measurability and measurable parameter integration for the actual heat Green function. -/
noncomputable section
open MeasureTheory Set Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.GreenHeatPointwise
open HeatDensityApproximation TorusHeatPositivity

theorem measurable_heatKernel_joint (d : ℕ) :
    Measurable (fun p : Torus d × ℝ => heatKernel p.2 p.1) := by
  unfold heatKernel torusTheta
  apply Complex.measurable_re.comp
  apply Measurable.tsum
  intro k
  apply Measurable.mul
  · apply Complex.measurable_ofReal.comp
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_snd).mul continuous_const)).measurable
  · exact ((UnitAddTorus.mFourier k).continuous.comp continuous_fst).measurable

theorem measurable_heatMellin_joint (d : ℕ) :
    Measurable (fun p : Torus d × ℝ => heatMellin p.1 p.2) := by
  exact (measurable_snd.pow_const ((d : ℝ)/2-1)).mul
    ((measurable_heatKernel_joint d).sub measurable_const)

theorem measurable_heatGreen (d : ℕ) : Measurable (heatGreen (d := d)) := by
  have hm : StronglyMeasurable (Function.uncurry (fun (x : Torus d) (t : ℝ) => heatMellin x t)) :=
    (measurable_heatMellin_joint d).stronglyMeasurable
  exact measurable_const.mul (hm.integral_prod_right (ν := volume.restrict (Ioi 0))).measurable

#print axioms measurable_heatGreen
end Legacy.BecknerOnofri.GreenHeatPointwise
