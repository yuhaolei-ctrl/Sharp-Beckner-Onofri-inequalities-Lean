import Legacy.BecknerOnofri.CosineMomentWeight
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Continuous moment functionals on the uniform function space used for
compact polarization-orbit selection. -/
noncomputable section
open scoped BoundedContinuousFunction
open MeasureTheory Legacy.TorusEndpoint
namespace BecknerOnofri.PolarizationL1

def boundedIntegral (d : ℕ) : (Torus d →ᵇ ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x,f x ∂torusMeasure d
     map_add' := by
       intro f g
       exact integral_add (f.integrable _) (g.integrable _)
     map_smul' := by
       intro c f
       exact integral_smul c f } : (Torus d →ᵇ ℝ) →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by
      change ‖∫ x,f x ∂torusMeasure d‖≤1*‖f‖
      simpa only [one_mul] using f.norm_integral_le_norm (torusMeasure d))

@[simp] lemma boundedIntegral_apply {d : ℕ} (f : Torus d →ᵇ ℝ) :
    boundedIntegral d f=∫ x,f x ∂torusMeasure d := rfl

theorem boundedMoment_continuous {d : ℕ} (w : Torus d →ᵇ ℝ) :
    Continuous (fun f : Torus d →ᵇ ℝ => ∫ x,f x*w x ∂torusMeasure d) := by
  exact (boundedIntegral d).continuous.comp (continuous_id.mul continuous_const)

#print axioms boundedMoment_continuous
end BecknerOnofri.PolarizationL1
