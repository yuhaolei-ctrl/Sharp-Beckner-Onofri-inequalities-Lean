import Legacy.BecknerOnofri.GreenDensityPotential

/-! Actual Green potentials of arbitrary L2 probability densities.  A direct
quadratic bound proves boundedness of their convolution, without assuming
continuity of the density or an abstract convolution theorem. -/
noncomputable section
namespace Legacy.BecknerOnofri.GreenDensityPotentialL2
open MeasureTheory Legacy.TorusEndpoint TorusSobolev GreenRoughEnergy SobolevDensityPairing

local instance (d : ℕ) : (torusMeasure d).IsAddLeftInvariant := by
  rw [torusMeasure_explicit]; infer_instance
local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have h : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [h]; infer_instance
local instance (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  rw [torusMeasure_explicit]; infer_instance

theorem potential_norm_bound {d : ℕ} (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) (x : Torus d) :
    ‖potential r x‖ ≤ (∫ y, kernel d y ^ 2 ∂torusMeasure d) +
      ∫ y, r.value y ^ 2 ∂torusMeasure d := by
  have hk := (kernel_memLp d).integrable_sq
  have ht : Integrable (fun y => kernel d (x-y)^2) (torusMeasure d) :=
    ((Measure.measurePreserving_sub_left (torusMeasure d) x).integrable_comp
      hk.aestronglyMeasurable).mpr hk
  calc
    _ ≤ ∫ y, ‖kernel d (x-y) * r.value y‖ ∂torusMeasure d := norm_integral_le_integral_norm _
    _ ≤ ∫ y, kernel d (x-y)^2 + r.value y^2 ∂torusMeasure d := by
      apply integral_mono_ae (potential_integrand_integrable r hr x).norm (ht.add hr.integrable_sq)
      filter_upwards [] with y
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      change |kernel d (x-y)| * |r.value y| ≤ kernel d (x-y)^2 + r.value y^2
      nlinarith only [sq_nonneg (|kernel d (x-y)| - |r.value y|),
        sq_abs (kernel d (x-y)), sq_abs (r.value y), sq_nonneg (kernel d (x-y)), sq_nonneg (r.value y)]
    _ = _ := by
      rw [integral_add ht hr.integrable_sq]
      congr 1
      exact integral_sub_left_eq_self (fun y => kernel d y ^ 2) (torusMeasure d) x

theorem potential_memLp {d : ℕ} (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    MemLp (potential r) 2 (torusMeasure d) :=
  MemLp.of_bound (potential_integrable r).aestronglyMeasurable _
    (Filter.Eventually.of_forall (potential_norm_bound r hr))

def potentialLp {d : ℕ} (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) : TorusL2 d :=
  (potential_memLp r hr).ofReal.toLp (fun x => (potential r x : ℂ))

theorem potentialLp_ae {d : ℕ} (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    potentialLp r hr =ᵐ[torusMeasure d] (fun x => (potential r x : ℂ)) :=
  (potential_memLp r hr).ofReal.coeFn_toLp

theorem potentialLp_fourier {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) (k : Frequency d) :
    fourierIsometry d (potentialLp r hr) k =
      (if k = 0 then 0 else (1 / frequencyRadius k^d : ℝ) : ℂ) * densityFourier r.value k :=
  (fourierIsometry_apply d _ k).trans
    ((GreenPairing.fourierCoeff_real_toLp (potential_memLp r hr) k).trans
      (GreenDensityPotential.potential_fourier hd r k))

theorem potentialLp_real {d : ℕ} (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    SubcriticalAttainment.RealPotential (potentialLp r hr) := by
  filter_upwards [potentialLp_ae r hr] with x hx
  simp [hx]

theorem potentialLp_weightedSquare {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) (k : Frequency d) :
    weightedSquare (fourierIsometry d (potentialLp r hr)) k = fullDensityTerm r k := by
  unfold weightedSquare
  rw [potentialLp_fourier hd]
  by_cases hk : k = 0
  · simp [hk, fullDensityTerm]
  · have hw : 0 < frequencyRadius k^d := pow_pos (frequencyRadius_pos hk) _
    simp only [if_neg hk, fullDensityTerm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (one_div_nonneg.mpr hw.le), mul_pow]
    field_simp

theorem potentialLp_admissible {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    SubcriticalAttainment.Admissible (potentialLp r hr) := by
  refine ⟨potentialLp_real r hr, ?_, ?_⟩
  · simp [potentialLp_fourier hd]
  · have he : weightedSquare (fourierIsometry d (potentialLp r hr)) = fullDensityTerm r :=
      funext (potentialLp_weightedSquare hd r hr)
    rw [he]
    exact (fullDensityTerm_hasSum hd r hr).summable

theorem potentialLp_energy {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    criticalEnergy (potentialLp r hr) = fourierEnergy r := by
  have he : weightedSquare (fourierIsometry d (potentialLp r hr)) = fullDensityTerm r :=
    funext (potentialLp_weightedSquare hd r hr)
  rw [criticalEnergy, coefficientEnergy, he, (fullDensityTerm_hasSum hd r hr).tsum_eq]

#print axioms potential_memLp
#print axioms potentialLp_admissible
#print axioms potentialLp_energy
end Legacy.BecknerOnofri.GreenDensityPotentialL2
