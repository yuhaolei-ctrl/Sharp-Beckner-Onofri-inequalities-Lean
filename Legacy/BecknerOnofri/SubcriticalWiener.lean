module

public import Legacy.BecknerOnofri.RadialWiener
public import Legacy.BecknerOnofri.SubcriticalEuler
public import Legacy.TorusEndpoint.GreenPairing

@[expose] public section

/-! The actual Euler equation upgrades every subcritical maximizer to Fourier
coefficients with absolutely summable polynomial moments of every order. -/

open MeasureTheory
open scoped BigOperators

namespace Legacy.BecknerOnofri.SubcriticalEuler

open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment WienerFourier RadialWiener
open GreenMultiplierSummability

theorem maximizer_fourier_green_formula {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (k : Frequency d) :
    fourierIsometry d u k = ((endpointSigma d/(2*A) : ℝ) : ℂ) *
      ((greenMultiplier d k : ℂ) * densityFourier (gibbsValue u) k) := by
  by_cases hk : k = 0
  · simp [hk, hu.2.1]
  · rw [maximizer_fourier_formula hR hA hu hmax hk, greenMultiplier_of_ne_zero hk]
    have hs : (endpointSigma d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (endpointSigma_pos hd).ne'
    have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
    have hr : (frequencyRadius k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (frequencyRadius_pos hk).ne'
    push_cast
    field_simp

theorem maximizer_fourier_summable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    Summable (fun k => ‖fourierIsometry d u k‖) := by
  have h := (GreenPairing.summable_realGreen_pairing_norm (gibbsValue_memLp_two hR hu)).mul_left
    ‖((endpointSigma d/(2*A) : ℝ) : ℂ)‖
  apply h.congr
  intro k
  simp only [maximizer_fourier_green_formula hd hR hA hu hmax k, norm_mul]

theorem maximizer_continuous_representative {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    Continuous (representative u) ∧ representative u =ᵐ[torusMeasure d] u ∧
      ∀ x, (representative u x).im = 0 := by
  have hs := maximizer_fourier_summable hd hR hA hu hmax
  exact ⟨representative_continuous u hs, representative_ae_eq u hs, representative_real u hs hu.1⟩

theorem maximizer_radialSummable_step {d : ℕ} {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (m : ℕ) (hm : RadialSummable (fourierIsometry d u) m) :
    RadialSummable (fourierIsometry d u) (m+d) := by
  have hg : RadialSummable (densityFourier (gibbsValue u)) m :=
    gibbs_radialSummable u m hm hu.1 (partition u)
  exact elliptic_step (by positivity : 0 < 2*A) hu.2.1
    (fun _ hk => maximizer_fourier_equation hR hu hmax hk) m hg

theorem maximizer_radialSummable_multiple {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (n : ℕ) : RadialSummable (fourierIsometry d u) (n*d) := by
  induction n with
  | zero =>
    rw [Nat.zero_mul, radialSummable_zero]
    exact maximizer_fourier_summable hd hR hA hu hmax
  | succ n ih =>
    rw [Nat.succ_mul]
    exact maximizer_radialSummable_step hR hA hu hmax (n*d) ih

theorem maximizer_radialSummable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (m : ℕ) : RadialSummable (fourierIsometry d u) m := by
  exact radialSummable_mono (by simpa using Nat.mul_le_mul_left m hd)
    (maximizer_radialSummable_multiple hd hR hA hu hmax m)

theorem maximizer_density_radialSummable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (m : ℕ) : RadialSummable (densityFourier (gibbsValue u)) m :=
  gibbs_radialSummable u m (maximizer_radialSummable hd hR hA hu hmax m) hu.1 (partition u)

#print axioms maximizer_fourier_summable
#print axioms maximizer_continuous_representative
#print axioms maximizer_radialSummable
#print axioms maximizer_density_radialSummable

end Legacy.BecknerOnofri.SubcriticalEuler
