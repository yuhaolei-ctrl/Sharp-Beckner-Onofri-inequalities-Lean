module

public import BecknerOnofri.Friedrichs.MixedAngularFiber
public import BecknerOnofri.Friedrichs.MixedFiberIntegral

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def angularOperatorImage {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ) (x : Space d) : ℝ :=
  ∑ i,angularCoordinateImage α f i x

lemma angularCoordinateImage_continuous {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) : Continuous (angularCoordinateImage α f i) := by
  exact (continuous_finsetProd _ (fun j _ => (angularProfiles_smooth α f hf j).continuous.comp
    (continuous_apply j))).mul ((angularImage_continuous (α i) (hf i)).comp (continuous_apply i))

lemma angularOperatorImage_continuous {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) : Continuous (angularOperatorImage α f) :=
  continuous_finsetSum _ (fun i _ => angularCoordinateImage_continuous α f hf i)

lemma angular_coordinate_weak {d : ℕ} (α : MultiIndex d) (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) {φ : Space d → ℝ}
    (hφ : smoothCoreProfile α φ) (i : Fin d)
    (hI : Integrable (fun x => partialDerivative i (angularFunction α f) x*partialDerivative i φ x+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*angularFunction α f x*φ x) (spatialMeasure α)) :
    (∫ x,partialDerivative i (angularFunction α f) x*partialDerivative i φ x+
      ((α i:ℝ)*((α i:ℝ)-1)/(Real.sin (x i))^2)*angularFunction α f x*φ x ∂spatialMeasure α)=
      ∫ x,angularCoordinateImage α f i x*φ x ∂spatialMeasure α := by
  apply integral_eq_of_fiber_eq α i hI
    ((continuous_memLp α ((angularCoordinateImage_continuous α f hf i).mul hφ.1.continuous)).integrable (by norm_num))
  intro x
  simpa only [Function.update_self,Pi.mul_apply] using angular_fiber_weak α f hf hφ i x

#print axioms angular_coordinate_weak
end BecknerOnofri.Friedrichs.MixedSpatial
