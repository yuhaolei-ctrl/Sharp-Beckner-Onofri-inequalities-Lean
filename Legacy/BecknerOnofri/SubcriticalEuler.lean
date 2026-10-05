import Legacy.BecknerOnofri.SubcriticalFourierVariation

/-! The Fourier Euler equation is derived from actual global maximality by real Fourier variations. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
open scoped BigOperators ComplexConjugate ENNReal
namespace Legacy.BecknerOnofri.SubcriticalEuler
open TorusSobolev SubcriticalAttainment

theorem densityFourier_conj_symmetry {d : ℕ} (rho : Torus d → ℝ) (k : Frequency d) :
    densityFourier rho (-k) = conj (densityFourier rho k) := by
  unfold densityFourier
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [neg_neg, map_mul, Complex.conj_ofReal, ← UnitAddTorus.mFourier_neg]

theorem gibbs_mode_pairing {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (k : Frequency d) (z : ℂ) :
    (∫ x, gibbsValue u x*(mode k z x).re ∂torusMeasure d) =
      2*((densityFourier (gibbsValue u) k)*conj z).re := by
  have hf (j : Frequency d) : Integrable (fun x => UnitAddTorus.mFourier (-j) x * (gibbsValue u x : ℂ))
      (torusMeasure d) := densityFourier_integrable (gibbsDensity hR hu) j
  have hp : Integrable (fun x => (gibbsValue u x : ℂ)*mode k z x) (torusMeasure d) :=
    (gibbsValue_memLp_two hR hu).ofReal.integrable_mul (Lp.memLp (mode k z))
  have he : (∫ x, (gibbsValue u x : ℂ)*mode k z x ∂torusMeasure d) =
      z*densityFourier (gibbsValue u) (-k)+conj z*densityFourier (gibbsValue u) k := by
    calc
      _ = ∫ x, z*(UnitAddTorus.mFourier (-(-k)) x*(gibbsValue u x : ℂ))+
          conj z*(UnitAddTorus.mFourier (-k) x*(gibbsValue u x : ℂ)) ∂torusMeasure d := by
        apply integral_congr_ae
        filter_upwards [mode_coe k z] with x hx
        rw [hx, neg_neg]
        ring
      _ = _ := by
        rw [integral_add ((hf (-k)).const_mul z) ((hf k).const_mul (conj z)),
          integral_const_mul, integral_const_mul]
        rfl
  have hr := congrArg Complex.re he
  have hir : (∫ x, (gibbsValue u x : ℂ)*mode k z x ∂torusMeasure d).re =
      ∫ x, ((gibbsValue u x : ℂ)*mode k z x).re ∂torusMeasure d := (integral_re hp).symm
  rw [hir, densityFourier_conj_symmetry] at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, Complex.conj_re, Complex.conj_im] at hr ⊢
  linarith

theorem perturb_pairing {d : ℕ} {b Ab : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u) (k : Frequency d) (z : ℂ) (t : ℝ) :
    (∫ x, gibbsValue u x*((perturb u k z t x).re-(u x).re) ∂torusMeasure d) =
      2*t*((densityFourier (gibbsValue u) k)*conj z).re := by
  calc
    _ = ∫ x, t*(gibbsValue u x*(mode k z x).re) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [perturb_coe u k z t] with x hx
      rw [hx]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    _ = _ := by rw [integral_const_mul, gibbs_mode_pairing hR hu]; ring

/-- A quadratic polynomial nonnegative on the real line has vanishing linear part at zero. -/
theorem linear_term_zero {a c : ℝ} (h : ∀ t : ℝ, a*t ≤ c*t^2) : a = 0 := by
  have hc : 0 ≤ c := by have h1 := h 1; have hm := h (-1); norm_num at h1 hm; linarith
  by_contra ha
  have hp : 0 < 2*(c+1) := by linarith
  have hh := h (a/(2*(c+1)))
  have hsq : 0 < a^2 := sq_pos_of_ne_zero ha
  field_simp at hh
  nlinarith

/-- All complex Fourier test parameters are obtained from real admissible trigonometric variations. -/
theorem maximizer_mode_equation {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    {k : Frequency d} (hk : k ≠ 0) (z : ℂ) :
    ((densityFourier (gibbsValue u) k)*conj z).re =
      2*A*frequencyRadius k^d*((fourierIsometry d u k)*conj z).re := by
  have hh (t : ℝ) := maximizer_variation_inequality hR hu hmax (perturb_admissible hu hk z t)
  simp_rw [perturb_pairing hR hu, energy_perturb hu hk] at hh
  have hzero := linear_term_zero (a := 2*((densityFourier (gibbsValue u) k)*conj z).re-
      4*A*frequencyRadius k^d*((fourierIsometry d u k)*conj z).re)
    (c := 2*A*frequencyRadius k^d*‖z‖^2) (by
      intro t
      have ht := hh t
      nlinarith only [ht])
  linarith

/-- The actual Gibbs density and actual Sobolev Fourier coefficients satisfy the Euler equation. -/
theorem maximizer_fourier_equation {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    {k : Frequency d} (hk : k ≠ 0) :
    densityFourier (gibbsValue u) k = ((2*A*frequencyRadius k^d : ℝ) : ℂ)*fourierIsometry d u k := by
  have hreal := maximizer_mode_equation hR hu hmax hk (1 : ℂ)
  have himag := maximizer_mode_equation hR hu hmax hk Complex.I
  apply Complex.ext
  · simpa only [map_one, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hreal
  · simpa only [Complex.conj_I, mul_neg, Complex.neg_re, Complex.mul_I_re, neg_neg,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using himag

theorem maximizer_fourier_formula {d : ℕ} {b Ab A : ℝ} (hR : RoughExponentialBound d b Ab)
    (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    {k : Frequency d} (hk : k ≠ 0) :
    fourierIsometry d u k = ((1/(2*A) * (frequencyRadius k^d)⁻¹ : ℝ) : ℂ)*densityFourier (gibbsValue u) k := by
  rw [maximizer_fourier_equation hR hu hmax hk]
  have hr : frequencyRadius k ≠ 0 := (frequencyRadius_pos hk).ne'
  have hp : frequencyRadius k^d ≠ 0 := pow_ne_zero _ hr
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hpc : (frequencyRadius k : ℂ)^d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr)
  push_cast
  field_simp [hAc, hpc]

#print axioms maximizer_fourier_equation
#print axioms maximizer_fourier_formula
end Legacy.BecknerOnofri.SubcriticalEuler
