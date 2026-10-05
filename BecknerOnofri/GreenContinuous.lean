import BecknerOnofri.BranchDefinitions
import Legacy.BecknerOnofri.GreenDensityPotential

/-! The actual normalized Green convolution as a bounded operator on real
continuous torus functions, with its exact Fourier multiplier. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Convolution

namespace BecknerOnofri.HighDim

local instance (d : ℕ) : (torusMeasure d).IsAddRightInvariant := by
  unfold torusMeasure
  infer_instance
local instance (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  unfold torusMeasure
  infer_instance
local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have h : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [h]
  infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  unfold torusMeasure
  infer_instance

def normalizedGreenKernel (d : ℕ) : Torus d → ℝ :=
  Legacy.BecknerOnofri.GreenRoughEnergy.kernel d

theorem normalizedGreenKernel_integrable (d : ℕ) :
    Integrable (normalizedGreenKernel d) (torusMeasure d) :=
  Legacy.BecknerOnofri.GreenRoughEnergy.kernel_integrable d

def greenKernelNorm (d : ℕ) : ℝ := ∫ x, ‖normalizedGreenKernel d x‖ ∂torusMeasure d

theorem greenKernelNorm_nonneg (d : ℕ) : 0 ≤ greenKernelNorm d :=
  integral_nonneg (fun _ => norm_nonneg _)

def greenContinuousValue {d : ℕ} (f : C(Torus d, ℝ)) (x : Torus d) : ℝ :=
  ∫ y, normalizedGreenKernel d y * f (x-y) ∂torusMeasure d

theorem green_integrand_integrable {d : ℕ} (f : C(Torus d, ℝ)) (x : Torus d) :
    Integrable (fun y => normalizedGreenKernel d y * f (x-y)) (torusMeasure d) :=
  (normalizedGreenKernel_integrable d).mul_bdd
    (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm (x-y)))

theorem greenContinuousValue_continuous {d : ℕ} (f : C(Torus d, ℝ)) :
    Continuous (greenContinuousValue f) := by
  change Continuous (normalizedGreenKernel d ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure d] f)
  exact (HasCompactSupport.of_compactSpace (f : Torus d → ℝ)).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (normalizedGreenKernel_integrable d).locallyIntegrable f.continuous

theorem greenContinuousValue_norm_le {d : ℕ} (f : C(Torus d, ℝ)) (x : Torus d) :
    ‖greenContinuousValue f x‖ ≤ greenKernelNorm d * ‖f‖ := by
  calc
    _ ≤ ∫ y, ‖normalizedGreenKernel d y * f (x-y)‖ ∂torusMeasure d := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖normalizedGreenKernel d y‖ * ‖f‖ ∂torusMeasure d := by
      apply integral_mono (green_integrand_integrable f x).norm
        ((normalizedGreenKernel_integrable d).norm.mul_const ‖f‖)
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def greenContinuousLinear (d : ℕ) : C(Torus d, ℝ) →ₗ[ℝ] C(Torus d, ℝ) where
  toFun f := ⟨greenContinuousValue f, greenContinuousValue_continuous f⟩
  map_add' f g := by
    ext x
    change (∫ y, normalizedGreenKernel d y * (f (x-y)+g (x-y)) ∂torusMeasure d) = _
    simp only [mul_add]
    exact integral_add (green_integrand_integrable f x) (green_integrand_integrable g x)
  map_smul' c f := by
    ext x
    change (∫ y, normalizedGreenKernel d y * (c*f (x-y)) ∂torusMeasure d) = _
    simp only [mul_left_comm (normalizedGreenKernel d _) c, integral_const_mul]
    rfl

/-- Actual Green operator C(T^d,ℝ)→C(T^d,ℝ), bounded by its L¹ kernel norm. -/
def greenContinuous (d : ℕ) : C(Torus d, ℝ) →L[ℝ] C(Torus d, ℝ) :=
  (greenContinuousLinear d).mkContinuous (greenKernelNorm d) (fun f => by
    apply (ContinuousMap.norm_le _ (mul_nonneg (greenKernelNorm_nonneg d) (norm_nonneg f))).mpr
    exact greenContinuousValue_norm_le f)

@[simp] theorem greenContinuous_apply {d : ℕ} (f : C(Torus d, ℝ)) (x : Torus d) :
    greenContinuous d f x = ∫ y, normalizedGreenKernel d y * f (x-y) ∂torusMeasure d := rfl

theorem greenContinuous_norm_le (d : ℕ) : ‖greenContinuous d‖ ≤ greenKernelNorm d := by
  apply ContinuousLinearMap.opNorm_le_bound _ (greenKernelNorm_nonneg d)
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg (greenKernelNorm_nonneg d) (norm_nonneg f))).mpr
  exact greenContinuousValue_norm_le f

theorem normalizedGreenKernel_fourier {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    fourierCoeff (normalizedGreenKernel d) k =
      ((if k = 0 then 0 else 1/frequencyLength k^d : ℝ):ℂ) := by
  simpa only [apply_ite Complex.ofReal, Complex.ofReal_zero, normalizedGreenKernel,
    fourierCoeff, frequencyLength, Legacy.TorusEndpoint.densityFourier,
    Legacy.TorusEndpoint.frequencyRadius, torusMeasure, Legacy.TorusEndpoint.torusMeasure_explicit] using
    Legacy.BecknerOnofri.GreenDensityPotential.kernel_fourier hd k

/-- Exact inverse critical-Laplacian multiplier for every real continuous input. -/
theorem greenContinuous_fourier {d : ℕ} (hd : 0 < d) (f : C(Torus d, ℝ)) (k : Frequency d) :
    fourierCoeff (greenContinuous d f) k =
      ((if k = 0 then 0 else 1/frequencyLength k^d : ℝ):ℂ) * fourierCoeff f k := by
  let F : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x * (normalizedGreenKernel d x : ℂ)
  let G : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x * (f x : ℂ)
  have hpoint (x : Torus d) : UnitAddTorus.mFourier (-k) x * (greenContinuous d f x : ℂ) =
      (F ⋆[ContinuousLinearMap.mul ℂ ℂ, torusMeasure d] G) x := by
    rw [greenContinuous_apply]
    rw [← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [F, G]
    have hc := Legacy.BecknerOnofri.HeatDensityApproximation.character_add (-k) y (x-y)
    rw [add_sub_cancel] at hc
    push_cast
    rw [hc]
    ring
  change (∫ x, UnitAddTorus.mFourier (-k) x * (greenContinuous d f x : ℂ) ∂torusMeasure d) = _
  simp_rw [hpoint]
  have hF : Integrable F (torusMeasure d) :=
    (normalizedGreenKernel_integrable d).ofReal.bdd_mul
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (Legacy.TorusEndpoint.fourier_character_norm_le_one (-k)))
  have hG : Integrable G (torusMeasure d) :=
    ((UnitAddTorus.mFourier (-k)).continuous.mul (Complex.continuous_ofReal.comp f.continuous))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hF hG]
  change fourierCoeff (normalizedGreenKernel d) k * fourierCoeff f k = _
  rw [normalizedGreenKernel_fourier hd]

#print axioms greenContinuous
#print axioms greenContinuous_fourier

end BecknerOnofri.HighDim
