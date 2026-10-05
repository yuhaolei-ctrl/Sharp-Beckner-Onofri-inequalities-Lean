module

public import Legacy.BecknerOnofri.Endpoint
public import Legacy.TorusEndpoint.TorusHeatBounds
public import Legacy.TorusEndpoint.GreenHeatRegularization
public import Legacy.TorusEndpoint.EntropyVariational
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

/-! Actual torus heat regularization of arbitrary probability densities. -/

noncomputable section
open MeasureTheory Legacy.TorusEndpoint Set Filter
open scoped Convolution Topology BigOperators

namespace Legacy.BecknerOnofri.HeatDensityApproximation
open TorusHeatBounds TorusHeatPositivity

local instance (d : ℕ) : (torusMeasure d).IsAddRightInvariant := by
  rw [torusMeasure_explicit]
  infer_instance

local instance (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  rw [torusMeasure_explicit]
  infer_instance

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance

local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  rw [torusMeasure_explicit]
  infer_instance

def heatKernel {d : ℕ} (t : ℝ) (x : Torus d) : ℝ := (torusTheta t x).re

theorem heatKernel_continuous {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Continuous (heatKernel (d := d) t) :=
  Complex.continuous_re.comp (torusTheta_continuous ht)

theorem heatKernel_pos {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Torus d) :
    0 < heatKernel t x := torusTheta_re_pos ht x

theorem heatKernel_integrable {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel (d := d) t) (torusMeasure d) :=
  (heatKernel_continuous ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem heatKernel_mass {d : ℕ} {t : ℝ} (ht : 0 < t) :
    (∫ x, heatKernel t x ∂torusMeasure d) = 1 := torusTheta_re_integral ht

def heatKernelDensity (d : ℕ) {t : ℝ} (ht : 0 < t) : ProbabilityDensity d where
  value := heatKernel t
  nonneg := Eventually.of_forall (fun x => (heatKernel_pos ht x).le)
  integrable := heatKernel_integrable ht
  mass := heatKernel_mass ht

def heatValue {d : ℕ} (rho : ProbabilityDensity d) (t : ℝ) : Torus d → ℝ :=
  rho.value ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure d] heatKernel t

theorem heatValue_integrand_integrable {d : ℕ} (rho : ProbabilityDensity d)
    {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Integrable (fun y => rho.value y * heatKernel t (x-y)) (torusMeasure d) :=
  (HasCompactSupport.of_compactSpace (heatKernel t)).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) rho.integrable.locallyIntegrable (heatKernel_continuous ht) x

theorem heatValue_continuous {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    Continuous (heatValue rho t) :=
  (HasCompactSupport.of_compactSpace (heatKernel t)).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) rho.integrable.locallyIntegrable (heatKernel_continuous ht)

theorem heatValue_integrable {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    Integrable (heatValue rho t) (torusMeasure d) :=
  rho.integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (heatKernel_integrable ht)

theorem heatValue_mass {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    (∫ x, heatValue rho t x ∂torusMeasure d) = 1 := by
  rw [heatValue, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    rho.integrable (heatKernel_integrable ht), rho.mass, heatKernel_mass ht]
  simp

theorem heatValue_pos {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t)
    (x : Torus d) : 0 < heatValue rho t x := by
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMinOn univ_nonempty (heatKernel_continuous ht).continuousOn
  have hpos := heatKernel_pos ht z
  have hi := integral_mono_ae (rho.integrable.mul_const (heatKernel t z))
    (heatValue_integrand_integrable rho ht x) (by
      filter_upwards [rho.nonneg] with y hy
      exact mul_le_mul_of_nonneg_left (hz (mem_univ (x-y))) hy)
  rw [integral_mul_const, rho.mass, one_mul] at hi
  exact hpos.trans_le hi

def heatDensity {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) : ProbabilityDensity d where
  value := heatValue rho t
  nonneg := Eventually.of_forall (fun x => (heatValue_pos rho ht x).le)
  integrable := heatValue_integrable rho ht
  mass := heatValue_mass rho ht

theorem heatDensity_finiteEntropy {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ} (ht : 0 < t) :
    (heatDensity rho ht).FiniteEntropy :=
  (Real.continuous_mul_log.comp (heatValue_continuous rho ht)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem character_add {d : ℕ} (k : Frequency d) (x y : Torus d) :
    UnitAddTorus.mFourier k (x+y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem heatKernel_fourier {d : ℕ} {t : ℝ} (ht : 0 < t) (k : Frequency d) :
    densityFourier (heatKernel (d := d) t) k = (heatWeight t k : ℂ) := by
  have he : (fun x : Torus d => (heatKernel t x : ℂ)) = torusTheta t := by
    funext x
    apply Complex.ext
    · rfl
    · simp [torusTheta_im_zero ht]
  change UnitAddTorus.mFourierCoeff (fun x : Torus d => (heatKernel t x : ℂ)) k = _
  rw [he]
  exact torusTheta_actual_fourierCoefficient ht k

theorem heatValue_fourier {d : ℕ} (rho : ProbabilityDensity d) {t : ℝ}
    (ht : 0 < t) (k : Frequency d) :
    densityFourier (heatValue rho t) k = (heatWeight t k : ℂ) * densityFourier rho.value k := by
  let f : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x * (rho.value x : ℂ)
  let g : Torus d → ℂ := fun x => UnitAddTorus.mFourier (-k) x * (heatKernel t x : ℂ)
  have hpoint (x : Torus d) :
      UnitAddTorus.mFourier (-k) x * (heatValue rho t x : ℂ) =
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ, torusMeasure d] g) x := by
    change _ * ((∫ y, rho.value y * heatKernel t (x-y) ∂torusMeasure d : ℝ) : ℂ) = _
    rw [← integral_complex_ofReal, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [f, g]
    have hc := character_add (-k) y (x-y)
    rw [add_sub_cancel] at hc
    push_cast
    rw [hc]
    ring
  change (∫ x, UnitAddTorus.mFourier (-k) x * (heatValue rho t x : ℂ) ∂torusMeasure d) = _
  simp_rw [hpoint]
  have hf : Integrable f (torusMeasure d) := densityFourier_integrable rho k
  have hg : Integrable g (torusMeasure d) := densityFourier_integrable (heatKernelDensity d ht) k
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    hf hg]
  change densityFourier rho.value k * densityFourier (heatKernel t) k = _
  rw [heatKernel_fourier ht, mul_comm]

theorem heatDensity_fourier_tendsto {d : ℕ} (rho : ProbabilityDensity d)
    (t : ℕ → ℝ) (hpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 0)) (k : Frequency d) :
    Tendsto (fun n => densityFourier (heatDensity rho (hpos n)).value k)
      atTop (𝓝 (densityFourier rho.value k)) := by
  simp only [heatDensity, heatValue_fourier rho (hpos _)]
  have h := (Complex.continuous_ofReal.tendsto 1).comp
    (GreenHeatRegularization.heatWeight_tendsto_one ht k)
  simpa using h.mul_const (densityFourier rho.value k)

theorem entropy_convolution_integrand_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (hr : rho.FiniteEntropy) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    Integrable (fun y => (rho.value y * Real.log (rho.value y)) * heatKernel t (x-y))
      (torusMeasure d) :=
  (HasCompactSupport.of_compactSpace (heatKernel t)).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hr.locallyIntegrable (heatKernel_continuous ht) x

/-- Jensen's inequality for this actual heat convolution, proved by integrating
the supporting line of r log r at its strictly positive smoothed value. -/
theorem heatValue_entropy_pointwise {d : ℕ} (rho : ProbabilityDensity d)
    (hr : rho.FiniteEntropy) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    heatValue rho t x * Real.log (heatValue rho t x) ≤
      ((fun y => rho.value y * Real.log (rho.value y))
        ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure d] heatKernel t) x := by
  let c := heatValue rho t x
  have hc : 0 < c := heatValue_pos rho ht x
  have hi := heatValue_integrand_integrable rho ht x
  have hk := (heatKernel_integrable ht).comp_sub_left x
  have he := entropy_convolution_integrand_integrable rho hr ht x
  have hbound := integral_mono_ae
    ((hi.mul_const (Real.log c+1)).sub (hk.const_mul c)) he (by
      filter_upwards [rho.nonneg] with y hy
      have h := entropy_young (rho.value y) (Real.log c) hy
      rw [Real.exp_log hc] at h
      have hh := mul_le_mul_of_nonneg_right h (heatKernel_pos ht (x-y)).le
      change rho.value y * heatKernel t (x-y) * (Real.log c+1) - c * heatKernel t (x-y) ≤
        rho.value y * Real.log (rho.value y) * heatKernel t (x-y)
      nlinarith)
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub (hi.mul_const _) (hk.const_mul _), integral_mul_const,
    integral_const_mul, integral_sub_left_eq_self, heatKernel_mass ht] at hbound
  change c * Real.log c ≤ ∫ y, rho.value y * Real.log (rho.value y) * heatKernel t (x-y)
    ∂torusMeasure d
  change c * (Real.log c + 1) - c * 1 ≤ _ at hbound
  nlinarith

/-- Heat smoothing contracts the genuine finite entropy. -/
theorem heatDensity_entropy_le {d : ℕ} (rho : ProbabilityDensity d)
    (hr : rho.FiniteEntropy) {t : ℝ} (ht : 0 < t) :
    densityEntropy (heatDensity rho ht).value ≤ densityEntropy rho.value := by
  have hi := hr.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (heatKernel_integrable ht)
  have h := integral_mono (heatDensity_finiteEntropy rho ht) hi
    (heatValue_entropy_pointwise rho hr ht)
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hr (heatKernel_integrable ht),
    heatKernel_mass ht] at h
  simpa only [ContinuousLinearMap.mul_apply', mul_one, densityEntropy] using! h

#print axioms heatValue_fourier
#print axioms heatValue_pos
#print axioms heatDensity_fourier_tendsto
#print axioms heatDensity_entropy_le

end Legacy.BecknerOnofri.HeatDensityApproximation
