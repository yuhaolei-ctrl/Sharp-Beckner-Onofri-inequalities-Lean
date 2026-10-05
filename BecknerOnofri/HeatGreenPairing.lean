import BecknerOnofri.MarginalKernelPairing
import Legacy.BecknerOnofri.GreenExponentialIntegrability
import Legacy.BecknerOnofri.LowDimensionPhysicalEndpoint

/-! Normalization of actual heat-kernel interactions and the one-dimensional
entropy bound for the coordinate reduction. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace BecknerOnofri.AdamsEndpoint
open Legacy.BecknerOnofri Legacy.TorusEndpoint.PhysicalGreenL2
open GreenHeatPointwise GreenExponentialIntegrability TorusMarginals

def heatInteraction {d : ℕ} (rho : ProbabilityDensity d) : ℝ :=
  ∫ x, ∫ y, heatGreen (x-y) * rho.value x * rho.value y ∂torusMeasure d ∂torusMeasure d

theorem heatInteraction_eq_physical {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d) :
    heatInteraction rho = physicalGreenEnergy rho := by
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply integral_congr_ae
  filter_upwards [(torus_sub_left_measurePreserving x).quasiMeasurePreserving.ae_eq
    (heatGreen_eq_realGreen_ae hd)] with y hy
  change heatGreen (x-y) * rho.value x * rho.value y = _
  dsimp only [Function.comp_apply] at hy
  rw [hy]

theorem circle_heatInteraction_entropy (rho : ProbabilityDensity 1) (hr : rho.FiniteEntropy) :
    heatInteraction rho ≤ densityEntropy rho.value := by
  rw [heatInteraction_eq_physical (by norm_num)]
  simpa using (physical_green_endpoint (by norm_num : 1 ≤ (1 : ℕ)) (by norm_num) rho hr).2

theorem coordinate_heatInteraction_entropy {n : ℕ}
    (rho : ProbabilityDensity (n+1)) (hr : Continuous rho.value)
    (hpos : ∀ x, 0 < rho.value x) (i : Fin (n+1)) :
    (∫ x, ∫ y, heatGreen (coordinateCircle i x-coordinateCircle i y) * rho.value x * rho.value y
      ∂torusMeasure (n+1) ∂torusMeasure (n+1)) ≤
      densityEntropy (torusMarginalDensity rho hr hpos i).value := by
  rw [torusMarginalDensity_kernel_pairing rho hr hpos i heatGreen (measurable_heatGreen 1)
    ((heatGreen_memLp (by norm_num : 0 < (1 : ℕ))).integrable (by norm_num))]
  exact circle_heatInteraction_entropy _ (torusMarginalDensity_finiteEntropy rho hr hpos i)

#print axioms heatInteraction_eq_physical
#print axioms coordinate_heatInteraction_entropy
end BecknerOnofri.AdamsEndpoint
