import BecknerOnofri.FiniteEntropyGreenPotential
import Legacy.BecknerOnofri.EndpointDensityFinitePotential

/-! The actual Green convolution on the entire finite-entropy domain, with
its exact critical Sobolev energy and pairing. -/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.FiniteEntropyGreen
open Legacy.TorusEndpoint Legacy.BecknerOnofri GreenRoughEnergy TorusSobolev SobolevDensityPairing

def potentialLp {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) : TorusL2 d :=
  (potential_memLp hd r hr).ofReal.toLp (fun x => (potential r x : ℂ))

theorem potentialLp_ae {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    potentialLp hd r hr =ᵐ[torusMeasure d] (fun x => (potential r x : ℂ)) :=
  (potential_memLp hd r hr).ofReal.coeFn_toLp

theorem potentialLp_fourier {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (k : Frequency d) :
    fourierIsometry d (potentialLp hd r hr) k =
      (if k = 0 then 0 else (1/frequencyRadius k^d : ℝ) : ℂ)*densityFourier r.value k :=
  (fourierIsometry_apply d _ k).trans
    ((GreenPairing.fourierCoeff_real_toLp (potential_memLp hd r hr) k).trans
      (GreenDensityPotential.potential_fourier hd r k))

theorem potentialLp_real {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    SubcriticalAttainment.RealPotential (potentialLp hd r hr) := by
  filter_upwards [potentialLp_ae hd r hr] with x hx
  simp [hx]

theorem potentialLp_weightedSquare {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) (k : Frequency d) :
    weightedSquare (fourierIsometry d (potentialLp hd r hr)) k = fullDensityTerm r k := by
  unfold weightedSquare
  rw [potentialLp_fourier]
  by_cases hk : k = 0
  · simp [hk,fullDensityTerm]
  · have hw : 0 < frequencyRadius k^d := pow_pos (frequencyRadius_pos hk) _
    simp only [if_neg hk,fullDensityTerm,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (one_div_nonneg.mpr hw.le),mul_pow]
    field_simp

lemma fullTerm_hasSum {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy) :
    HasSum (fullDensityTerm r) (fourierEnergy r) :=
  EndpointDensityFinitePotential.fullTerm_hasSum r
    (HighDim.FiniteEntropyPhysical.summable_energy hd r hr)

theorem potentialLp_admissible {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : SubcriticalAttainment.Admissible (potentialLp hd r hr) := by
  refine ⟨potentialLp_real hd r hr,?_,?_⟩
  · simp [potentialLp_fourier]
  · rw [funext (potentialLp_weightedSquare hd r hr)]
    exact (fullTerm_hasSum hd r hr).summable

theorem potentialLp_energy {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : criticalEnergy (potentialLp hd r hr) = fourierEnergy r := by
  rw [criticalEnergy,coefficientEnergy,funext (potentialLp_weightedSquare hd r hr),
    (fullTerm_hasSum hd r hr).tsum_eq]

theorem pairing_integrable {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : Integrable (fun x => r.value x*potential r x) (torusMeasure d) := by
  obtain ⟨C,hC⟩ := potential_bounded hd r hr
  exact r.integrable.mul_bdd (potential_integrable r).aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem pairing_eq_fourier {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : r.FiniteEntropy) : (∫ x,r.value x*potential r x ∂torusMeasure d) = fourierEnergy r := by
  rw [pairing_eq_physical,HighDim.FiniteEntropyPhysical.physical_eq_spectral hd r hr,
    normalized_energy]
  field_simp [(endpointSigma_pos hd).ne']

#print axioms potentialLp_admissible
#print axioms potentialLp_energy
#print axioms pairing_integrable
#print axioms pairing_eq_fourier
end BecknerOnofri.FiniteEntropyGreen
