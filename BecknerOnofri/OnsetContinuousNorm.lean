module

public import BecknerOnofri.OnsetWienerConvergence
public import BecknerOnofri.ContinuousFirstShell

@[expose] public section

/-! The uniform norm of a continuous potential on the torus is controlled by its absolutely
convergent Fourier series. This statement is split out of `OnsetContinuous` so that the
Sobolev embedding does not depend on the Euler-equation regularity modules. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.OnsetContinuous
open ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SobolevCentering
open BecknerOnofri.OnsetWienerBounds

/-- The uniform norm is controlled by the actual absolutely convergent Fourier series. -/
theorem norm_le_wiener {d : ℕ} (u : Space d)
    (hu : Summable (fun k => ‖coefficient k u‖)) :
    ‖u‖ ≤ radialSize 0 (fun k => coefficient k u) := by
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  have he : Legacy.BecknerOnofri.WienerFourier.representative (toL2 d u) = fun x => (u x : ℂ) :=
    Measure.eq_of_ae_eq
      ((Legacy.BecknerOnofri.WienerFourier.representative_ae_eq (toL2 d u) hu).trans (toL2_ae u))
      (Legacy.BecknerOnofri.WienerFourier.representative_continuous (toL2 d u) hu)
      (Complex.continuous_ofReal.comp u.continuous)
  apply (ContinuousMap.norm_le _ (radialSize_nonneg _ _)).mpr
  intro x
  have hs : Summable (fun k => ‖coefficient k u * UnitAddTorus.mFourier k x‖) := by
    simpa only [norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply, mul_one] using hu
  calc
    ‖u x‖ = ‖Legacy.BecknerOnofri.WienerFourier.representative (toL2 d u) x‖ := by
      rw [he, Complex.norm_real]
    _ ≤ ∑' k, ‖coefficient k u * UnitAddTorus.mFourier k x‖ := norm_tsum_le_tsum_norm hs
    _ = _ := by simp [radialSize, Legacy.BecknerOnofri.RadialWiener.radialWeight,
      norm_mul, Legacy.TorusEndpoint.mFourier_norm_apply]

end BecknerOnofri.HighDim.OnsetContinuous
