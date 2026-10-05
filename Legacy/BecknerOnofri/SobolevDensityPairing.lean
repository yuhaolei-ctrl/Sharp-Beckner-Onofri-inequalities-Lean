import Legacy.BecknerOnofri.SubcriticalAttainmentDefs
import Legacy.BecknerOnofri.Endpoint
import Legacy.TorusEndpoint.GreenPairing

/-! Actual Fourier pairings between critical Sobolev potentials and L2 densities.
The infinite-dimensional quadratic estimate follows from Parseval and a
pointwise completion of the square, with all three series summable.
-/
namespace Legacy.BecknerOnofri.SobolevDensityPairing
open MeasureTheory Legacy.TorusEndpoint TorusSobolev
open scoped BigOperators ComplexConjugate

theorem quadratic_scalar {b w p x y : ℝ} (hb : 0 < b) (hw : 0 < w) :
    p*x*y ≤ (p^2/(4*b))*w*x^2 + b*(y^2/w) := by
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4*b*w)).mp
  field_simp
  nlinarith [sq_nonneg (p*w*x-2*b*y)]

theorem quadratic_complex {b w p : ℝ} (hb : 0 < b) (hw : 0 < w) (hp : 0 ≤ p)
    (z v : ℂ) :
    p*(conj z*v).re ≤ (p^2/(4*b))*w*‖z‖^2 + b*(‖v‖^2/w) := by
  have h := mul_le_mul_of_nonneg_left (Complex.re_le_norm (conj z*v)) hp
  simp only [norm_mul] at h
  exact h.trans (by simpa [mul_assoc] using quadratic_scalar (p := p) (x := ‖z‖) (y := ‖v‖) hb hw)

noncomputable def fullDensityTerm {d : ℕ} (r : ProbabilityDensity d) (k : Frequency d) : ℝ :=
  if k = 0 then 0 else ‖densityFourier r.value k‖^2 / frequencyRadius k^d

theorem fullDensityTerm_hasSum {d : ℕ} (hd : 0 < d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) : HasSum (fullDensityTerm r) (fourierEnergy r) := by
  have hsupp : Function.support (fullDensityTerm r) ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hk0
    subst k
    simp [fullDensityTerm] at hk
  apply (hasSum_subtype_iff_of_support_subset hsupp).1
  have h := (PhysicalGreenL2.physicalGreenEnergy_eq_spectral hd r hr).1.hasSum
  have h' : HasSum (fun k : NonzeroFrequency d => fullDensityTerm r k.val) (fourierEnergy r) :=
    h.congr_fun (fun k => by simp only [fullDensityTerm, if_neg k.property, densitySpectralTerm])
  exact h'

theorem hasSum_pairing {d : ℕ} (u : TorusL2 d) (r : ProbabilityDensity d)
    (hr : MemLp r.value 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d =>
      (conj (fourierIsometry d u k) * densityFourier r.value k).re)
      (∫ x, r.value x * (u x).re ∂torusMeasure d) := by
  have hrc : MemLp (fun x => (r.value x : ℂ)) 2 (torusMeasure d) := hr.ofReal
  let R : TorusL2 d := hrc.toLp (fun x => (r.value x : ℂ))
  have hc : HasSum (fun k : Frequency d => conj (UnitAddTorus.mFourierCoeff u k) *
      UnitAddTorus.mFourierCoeff R k) (∫ x, conj (u x)*R x ∂torusMeasure d) :=
    UnitAddTorus.hasSum_prod_mFourierCoeff u R
  have h := Complex.hasSum_re hc
  have hi : Integrable (fun x => conj (u x)*R x) (torusMeasure d) :=
    (Lp.memLp u).star.integrable_mul (Lp.memLp R)
  have he : (∫ x, conj (u x)*R x ∂torusMeasure d).re =
      ∫ x, r.value x*(u x).re ∂torusMeasure d := by
    calc
      _ = ∫ x, (conj (u x)*R x).re ∂torusMeasure d := (integral_re hi).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hrc.coeFn_toLp] with x hx
        change R x = (r.value x : ℂ) at hx
        rw [hx]
        simp [Complex.mul_re, mul_comm]
  rw [he] at h
  simpa only [R, GreenPairing.fourierCoeff_real_toLp hr, fourierIsometry_apply] using h

theorem pairing_quadratic_bound {d : ℕ} (hd : 0 < d) (u : TorusL2 d)
    (hu : CriticalSobolev u) (r : ProbabilityDensity d) (hr : MemLp r.value 2 (torusMeasure d))
    (b : ℝ) (hb : 0 < b) (p : ℝ) (hp : 0 ≤ p) :
    p * (∫ x, r.value x * (u x).re ∂torusMeasure d) ≤
      p^2 * criticalEnergy u / (4*b) + b * fourierEnergy r := by
  have hleft := (hasSum_pairing u r hr).mul_left p
  have hright := (hu.2.hasSum.mul_left (p^2/(4*b))).add ((fullDensityTerm_hasSum hd r hr).mul_left b)
  have hpoint (k : Frequency d) :
      p * (conj (fourierIsometry d u k) * densityFourier r.value k).re ≤
        (p^2/(4*b)) * weightedSquare (fourierIsometry d u) k + b * fullDensityTerm r k := by
    by_cases hk : k = 0
    · simp [hk, hu.1, weightedSquare, fullDensityTerm]
    · have hw : 0 < frequencyRadius k^d := pow_pos (lt_of_lt_of_le zero_lt_one (radius_one_le hk)) _
      simpa only [weightedSquare, fullDensityTerm, if_neg hk, mul_assoc] using
        quadratic_complex hb hw hp (fourierIsometry d u k) (densityFourier r.value k)
  have h := hleft.summable.tsum_le_tsum hpoint hright.summable
  rw [hleft.tsum_eq, hright.tsum_eq] at h
  simpa only [criticalEnergy, coefficientEnergy, Pi.add_apply, div_mul_eq_mul_div] using h

#print axioms pairing_quadratic_bound
end Legacy.BecknerOnofri.SobolevDensityPairing
