import Legacy.BecknerOnofri.SubcriticalEuler
import Legacy.BecknerOnofri.SobolevDensityPairing

/-! Exact density/potential energy identities for the actually derived Euler pair. -/
namespace Legacy.BecknerOnofri.SubcriticalEuler
open MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SobolevDensityPairing
open scoped ComplexConjugate

theorem maximizer_densityTerm {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (k : Frequency d) :
    fullDensityTerm (gibbsDensity hR hu) k = (2*A)^2 * weightedSquare (fourierIsometry d u) k := by
  by_cases hk : k = 0
  · simp [hk, fullDensityTerm, weightedSquare, hu.2.1]
  · have hw := pow_ne_zero d (frequencyRadius_pos hk).ne'
    unfold fullDensityTerm
    rw [if_neg hk]
    change ‖densityFourier (gibbsValue u) k‖^2 / frequencyRadius k^d = _
    rw [maximizer_fourier_equation hR hu hmax hk]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, weightedSquare]
    field_simp

theorem maximizer_density_energy {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    fourierEnergy (gibbsDensity hR hu) = (2*A)^2 * criticalEnergy u := by
  have h := fullDensityTerm_hasSum hd (gibbsDensity hR hu) (gibbsValue_memLp_two hR hu)
  have he : fullDensityTerm (gibbsDensity hR hu) =
      fun k => (2*A)^2 * weightedSquare (fourierIsometry d u) k :=
    funext (maximizer_densityTerm hR hu hmax)
  rw [← h.tsum_eq, he, tsum_mul_left]
  rfl

theorem maximizer_pairing_term {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (k : Frequency d) :
    (conj (fourierIsometry d u k) * densityFourier (gibbsValue u) k).re =
      2*A * weightedSquare (fourierIsometry d u) k := by
  by_cases hk : k = 0
  · simp [hk, hu.2.1, weightedSquare]
  · rw [maximizer_fourier_equation hR hu hmax hk]
    simp only [weightedSquare, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem maximizer_pairing {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    (∫ x, gibbsValue u x * (u x).re ∂torusMeasure d) = 2*A * criticalEnergy u := by
  have h := hasSum_pairing u (gibbsDensity hR hu) (gibbsValue_memLp_two hR hu)
  have he : (fun k => (conj (fourierIsometry d u k) * densityFourier (gibbsDensity hR hu).value k).re) =
      fun k => 2*A * weightedSquare (fourierIsometry d u) k :=
    funext (maximizer_pairing_term hR hu hmax)
  change (∫ x, (gibbsDensity hR hu).value x * (u x).re ∂torusMeasure d) = _
  rw [← h.tsum_eq, he, tsum_mul_left]
  rfl

theorem maximizer_functional_eq_density {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (_hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    functional A u = (1/(4*A)) * fourierEnergy (gibbsDensity hR hu) - densityEntropy (gibbsValue u) := by
  rw [maximizer_density_energy hd hR hu hmax, gibbsDensity_entropy hR hu, maximizer_pairing hR hu hmax]
  unfold functional
  field_simp
  ring

#print axioms maximizer_density_energy
#print axioms maximizer_functional_eq_density
end Legacy.BecknerOnofri.SubcriticalEuler
