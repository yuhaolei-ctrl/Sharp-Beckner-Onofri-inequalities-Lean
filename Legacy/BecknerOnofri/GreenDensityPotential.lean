module

public import Legacy.BecknerOnofri.GreenConvolutionJensen
public import Legacy.BecknerOnofri.SobolevDensityPairing
public import Legacy.BecknerOnofri.HeatDensityApproximation

@[expose] public section

/-! The actual Green convolution of a continuous density is a real critical
Sobolev potential, with exact Fourier coefficients and energy.
-/
noncomputable section
namespace Legacy.BecknerOnofri.GreenDensityPotential
open MeasureTheory Legacy.TorusEndpoint TorusSobolev GreenRoughEnergy SobolevDensityPairing
open scoped Convolution

local instance (d : ℕ) : (torusMeasure d).IsAddRightInvariant := by
  rw [torusMeasure_explicit]; infer_instance
local instance (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  rw [torusMeasure_explicit]; infer_instance
local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have h : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [h]; infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  rw [torusMeasure_explicit]; infer_instance

theorem potential_eq_convolution {d : ℕ} (r : ProbabilityDensity d) :
    potential r = r.value ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure d] kernel d := by
  funext x
  unfold potential convolution
  apply integral_congr_ae
  filter_upwards [] with y
  simp [mul_comm]

theorem potential_continuous {d : ℕ} (r : ProbabilityDensity d) (hc : Continuous r.value) :
    Continuous (potential r) := by
  rw [potential_eq_convolution]
  exact (HasCompactSupport.of_compactSpace r.value).continuous_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) hc (kernel_integrable d).locallyIntegrable

theorem potential_memLp {d : ℕ} (r : ProbabilityDensity d) (hc : Continuous r.value) :
    MemLp (potential r) 2 (torusMeasure d) :=
  (potential_continuous r hc).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem kernel_fourier {d : ℕ} (hd : 0 < d) (k : Frequency d) :
    densityFourier (kernel d) k =
      (if k = 0 then 0 else (1 / frequencyRadius k^d : ℝ) : ℂ) := by
  have hs := (endpointSigma_pos hd).ne'
  have hf : densityFourier (kernel d) k =
      (endpointSigma d : ℂ) * densityFourier (GreenKernelReal.realGreen d) k := by
    unfold densityFourier kernel
    simp only [Complex.ofReal_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hf, GreenKernelReal.realGreen_fourierCoeff, ← Complex.ofReal_mul]
  by_cases hk : k = 0
  · simp [hk, GreenMultiplierSummability.greenMultiplier]
  · rw [if_neg hk]
    apply congrArg Complex.ofReal
    simp only [GreenMultiplierSummability.greenMultiplier, if_neg hk]
    field_simp

theorem potential_fourier {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d) (k : Frequency d) :
    densityFourier (potential r) k =
      (if k = 0 then 0 else (1 / frequencyRadius k^d : ℝ) : ℂ) * densityFourier r.value k := by
  let f : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x * (r.value x : ℂ)
  let g : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x * (kernel d x : ℂ)
  have hpoint (x : Torus d) : UnitAddTorus.mFourier (-k) x * (potential r x : ℂ) =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ, torusMeasure d] g) x := by
    rw [potential_eq_convolution]
    change _ * ((∫ y, r.value y * kernel d (x-y) ∂torusMeasure d : ℝ) : ℂ) = _
    rw [← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [f, g]
    have hc := HeatDensityApproximation.character_add (-k) y (x-y)
    rw [add_sub_cancel] at hc
    push_cast
    rw [hc]
    ring
  change (∫ x, UnitAddTorus.mFourier (-k) x * (potential r x : ℂ) ∂torusMeasure d) = _
  simp_rw [hpoint]
  have hf : Integrable f (torusMeasure d) := densityFourier_integrable r k
  have hg : Integrable g (torusMeasure d) := by
    apply (kernel_integrable d).ofReal.bdd_mul
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fourier_character_norm_le_one (-k))
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf hg]
  change densityFourier r.value k * densityFourier (kernel d) k = _
  rw [kernel_fourier hd, mul_comm]

def potentialLp {d : ℕ} (r : ProbabilityDensity d) (hc : Continuous r.value) : TorusL2 d :=
  (potential_memLp r hc).ofReal.toLp (fun x => (potential r x : ℂ))

theorem potentialLp_fourier {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hc : Continuous r.value) (k : Frequency d) :
    fourierIsometry d (potentialLp r hc) k =
      (if k = 0 then 0 else (1 / frequencyRadius k^d : ℝ) : ℂ) * densityFourier r.value k :=
  (fourierIsometry_apply d _ k).trans
    ((GreenPairing.fourierCoeff_real_toLp (potential_memLp r hc) k).trans (potential_fourier hd r k))

theorem potentialLp_real {d : ℕ} (r : ProbabilityDensity d) (hc : Continuous r.value) :
    SubcriticalAttainment.RealPotential (potentialLp r hc) := by
  have h : (potentialLp r hc) =ᵐ[torusMeasure d] (fun x => (potential r x : ℂ)) :=
    (potential_memLp r hc).ofReal.coeFn_toLp
  filter_upwards [h] with x hx
  simp [hx]

theorem potentialLp_weightedSquare {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hc : Continuous r.value) (k : Frequency d) :
    weightedSquare (fourierIsometry d (potentialLp r hc)) k = fullDensityTerm r k := by
  unfold weightedSquare
  rw [potentialLp_fourier hd]
  by_cases hk : k = 0
  · simp [hk, fullDensityTerm]
  · have hw : 0 < frequencyRadius k^d := pow_pos (lt_of_lt_of_le zero_lt_one (radius_one_le hk)) _
    simp only [if_neg hk, fullDensityTerm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (one_div_nonneg.mpr hw.le), mul_pow]
    field_simp

theorem potentialLp_admissible {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hc : Continuous r.value) : SubcriticalAttainment.Admissible (potentialLp r hc) := by
  refine ⟨potentialLp_real r hc, ?_, ?_⟩
  · simp [potentialLp_fourier hd]
  · have hr : MemLp r.value 2 (torusMeasure d) :=
      hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he : weightedSquare (fourierIsometry d (potentialLp r hc)) = fullDensityTerm r :=
      funext (potentialLp_weightedSquare hd r hc)
    rw [he]
    exact (fullDensityTerm_hasSum hd r hr).summable

theorem potentialLp_energy {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hc : Continuous r.value) : criticalEnergy (potentialLp r hc) = fourierEnergy r := by
  have hr : MemLp r.value 2 (torusMeasure d) :=
    hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : weightedSquare (fourierIsometry d (potentialLp r hc)) = fullDensityTerm r :=
    funext (potentialLp_weightedSquare hd r hc)
  rw [criticalEnergy, coefficientEnergy, he, (fullDensityTerm_hasSum hd r hr).tsum_eq]

#print axioms potential_fourier
#print axioms potentialLp_admissible
#print axioms potentialLp_energy
end Legacy.BecknerOnofri.GreenDensityPotential
