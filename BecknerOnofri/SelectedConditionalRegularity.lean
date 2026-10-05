module

public import BecknerOnofri.SelectedSpinEntropy
public import BecknerOnofri.ConditionalFourierRegularity
public import Legacy.BecknerOnofri.ChebyshevProfileIdentification

@[expose] public section

/-! Smoothness of the actual selected optimizer's conditional circles. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier RadialWiener

theorem spinDensity_radialSummable {u : TorusL2 12} (hu : Selected u) (m : ℕ) :
    RadialSummable (densityFourier (spinDensity hu).value) m := by
  have he : densityFourier (spinDensity hu).value = densityFourier (gibbsValue u) :=
    funext (smoothGibbsDensity_fourier rough hu.1 (fourier_norm_summable hu))
  rw [he]
  exact maximizer_density_radialSummable (by norm_num) rough (by norm_num : (0 : ℝ) < 1/2)
    hu.1 hu.2.1 m

theorem spinDensity_fourierSeries {u : TorusL2 12} (hu : Selected u) :
    ∀ x, ((spinDensity hu).value x : ℂ) =
      absoluteFourierSeries (densityFourier (spinDensity hu).value) x := by
  have h := ChebyshevProfile.continuous_eq_fourierSeries (spinDensity hu).value
    (smoothGibbsValue_continuous u (fourier_norm_summable hu))
    ((radialSummable_zero _).mp (spinDensity_radialSummable hu 0))
  exact fun x => (congrFun h x).symm

theorem selected_conditional_contDiff {u : TorusL2 12} (hu : Selected u)
    (i : Fin 12) (x : HighDim.Torus 12) :
    ContDiff ℝ ∞ (fun t : ℝ => ConditionalEntropy.conditionalDensity
      (spinDensity hu).value i x (t : UnitAddCircle)) :=
  ConditionalEntropy.conditional_density_contDiff _ (spinDensity_radialSummable hu)
    _ (spinDensity_fourierSeries hu) i x

#print axioms selected_conditional_contDiff
end BecknerOnofri.HighDim.SelectedNumericalModel
