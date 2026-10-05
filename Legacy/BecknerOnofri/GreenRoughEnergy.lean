import Legacy.BecknerOnofri.Endpoint
import Legacy.TorusEndpoint.EntropyVariational

/-! Rough entropy control by the actual normalized Green kernel.
The exponential integrability of that actual kernel is an explicit intermediate input.
The kernel pairing and the spectral energy identity are proved, not assumed.
-/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.GreenRoughEnergy
open GreenKernelReal PhysicalGreenL2

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance

def kernel (d : ℕ) (x : Torus d) : ℝ := endpointSigma d * realGreen d x

def partition (d : ℕ) (b : ℝ) : ℝ :=
  ∫ x, Real.exp (b * kernel d x) ∂torusMeasure d

def potential {d : ℕ} (rho : ProbabilityDensity d) (x : Torus d) : ℝ :=
  ∫ y, kernel d (x-y) * rho.value y ∂torusMeasure d

theorem kernel_memLp (d : ℕ) : MemLp (kernel d) 2 (torusMeasure d) :=
  (realGreen_memLp d).const_mul _

theorem kernel_integrable (d : ℕ) : Integrable (kernel d) (torusMeasure d) :=
  (realGreen_integrable d).const_mul _

private theorem sub_left_preserving {d : ℕ} (x : Torus d) :
    MeasurePreserving (fun y => x-y) (torusMeasure d) (torusMeasure d) := by
  letI : (torusMeasure d).IsAddLeftInvariant := by rw [torusMeasure_explicit]; infer_instance
  letI : (torusMeasure d).IsNegInvariant := by rw [torusMeasure_explicit]; infer_instance
  exact Measure.measurePreserving_sub_left _ x

private theorem integral_sub_left {d : ℕ} (f : Torus d → ℝ) (x : Torus d) :
    (∫ y, f (x-y) ∂torusMeasure d) = ∫ y, f y ∂torusMeasure d := by
  letI : (torusMeasure d).IsAddLeftInvariant := by rw [torusMeasure_explicit]; infer_instance
  letI : (torusMeasure d).IsNegInvariant := by rw [torusMeasure_explicit]; infer_instance
  exact integral_sub_left_eq_self f _ x

theorem potential_integrand_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) (x : Torus d) :
    Integrable (fun y => kernel d (x-y) * rho.value y) (torusMeasure d) :=
  ((kernel_memLp d).comp_measurePreserving (sub_left_preserving x)).integrable_mul hr

/-- Pointwise entropy control by the actual translated kernel for every L2 density. -/
theorem potential_entropy_bound {d : ℕ} (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) (b : ℝ)
    (hexp : Integrable (fun x => Real.exp (b * kernel d x)) (torusMeasure d))
    (x : Torus d) :
    b * potential rho x ≤ densityEntropy rho.value + Real.log (partition d b) := by
  have hu : Integrable (fun y => rho.value y * (b * kernel d (x-y))) (torusMeasure d) := by
    convert! (potential_integrand_integrable rho hr x).const_mul b using 1
    funext y
    ring
  have he : Integrable (fun y => Real.exp (b * kernel d (x-y))) (torusMeasure d) :=
    ((sub_left_preserving x).integrable_comp hexp.aestronglyMeasurable).mpr hexp
  have h := entropy_variational_of_integrable rho.nonneg rho.mass rho.integrable
    (finiteEntropy_of_memLp rho hr) hu he
  have hi : (∫ y, rho.value y * (b * kernel d (x-y)) ∂torusMeasure d) = b * potential rho x := by
    rw [potential, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by ring)
  rw [hi, integral_sub_left (fun y => Real.exp (b * kernel d y)) x] at h
  change b * potential rho x - Real.log (partition d b) ≤ densityEntropy rho.value at h
  linarith

theorem pairing_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) :
    Integrable (fun x => rho.value x * potential rho x) (torusMeasure d) := by
  have hi := (kernelInteraction_integrable rho hr (kernel d) (kernel_memLp d)).integral_prod_left
  convert! hi using 1
  funext x
  rw [potential, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

/-- The convolution pairing is the physical Green double integral with its actual normalization. -/
theorem pairing_eq_physical {d : ℕ} (rho : ProbabilityDensity d) :
    (∫ x, rho.value x * potential rho x ∂torusMeasure d) =
      endpointSigma d * physicalGreenEnergy rho := by
  simp only [potential, physicalGreenEnergy, kernel]
  simp_rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by ring)

/-- The unconditional pairing-to-spectrum step for a genuine L2 density. -/
theorem pairing_eq_fourier {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) :
    (∫ x, rho.value x * potential rho x ∂torusMeasure d) = fourierEnergy rho := by
  rw [pairing_eq_physical, (physicalGreenEnergy_eq_spectral hd rho hr).2, normalized_energy]
  field_simp [(endpointSigma_pos hd).ne']

/-- Rough energy estimate for every genuine L2 probability density.
The only kernel input is integrability of its displayed exponential. -/
theorem rough_energy {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hr : MemLp rho.value 2 (torusMeasure d)) (b : ℝ)
    (hexp : Integrable (fun x => Real.exp (b * kernel d x)) (torusMeasure d)) :
    b * fourierEnergy rho ≤ densityEntropy rho.value + Real.log (partition d b) := by
  have h := integral_mono_ae ((pairing_integrable rho hr).const_mul b)
    (rho.integrable.mul_const (densityEntropy rho.value + Real.log (partition d b)))
    (by
      filter_upwards [rho.nonneg] with x hx
      have h := mul_le_mul_of_nonneg_left (potential_entropy_bound rho hr b hexp x) hx
      convert! h using 1 <;> ring)
  rw [integral_const_mul, pairing_eq_fourier hd rho hr, integral_mul_const, rho.mass, one_mul] at h
  exact h

theorem rough_energy_continuous {d : ℕ} (hd : 0 < d) (rho : ProbabilityDensity d)
    (hr : Continuous rho.value) (b : ℝ)
    (hexp : Integrable (fun x => Real.exp (b * kernel d x)) (torusMeasure d)) :
    b * fourierEnergy rho ≤ densityEntropy rho.value + Real.log (partition d b) :=
  rough_energy hd rho (hr.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) b hexp

#print axioms potential_entropy_bound
#print axioms pairing_eq_fourier
#print axioms rough_energy
end Legacy.BecknerOnofri.GreenRoughEnergy
