module

public import Legacy.BecknerOnofri.WeightedWiener
public import Legacy.BecknerOnofri.WienerRepresentative

@[expose] public section

/-! Polynomial Euclidean frequency weights for the complex Wiener algebra. -/

open scoped BigOperators

namespace Legacy.BecknerOnofri.RadialWiener

open Legacy.TorusEndpoint WienerFourier WeightedWiener TorusSobolev

noncomputable def frequencyVector {d : ℕ} (k : Frequency d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

theorem norm_frequencyVector {d : ℕ} (k : Frequency d) :
    ‖frequencyVector k‖ = frequencyRadius k := by
  rw [EuclideanSpace.norm_eq]
  simp only [frequencyVector, Real.norm_eq_abs, sq_abs, frequencyRadius]

theorem frequencyVector_add {d : ℕ} (k l : Frequency d) :
    frequencyVector (k+l) = frequencyVector k + frequencyVector l := by
  ext i
  simp [frequencyVector]

theorem frequencyRadius_add_le {d : ℕ} (k l : Frequency d) :
    frequencyRadius (k+l) ≤ frequencyRadius k + frequencyRadius l := by
  simpa only [← norm_frequencyVector, frequencyVector_add] using
    norm_add_le (frequencyVector k) (frequencyVector l)

noncomputable def radialWeight {d : ℕ} (m : ℕ) (k : Frequency d) : ℝ :=
  (1 + frequencyRadius k)^m

theorem radialWeight_isWeight {d : ℕ} (m : ℕ) : IsWeight (radialWeight (d := d) m) where
  one_le k := one_le_pow₀ (by linarith [frequencyRadius_nonneg k])
  zero := by simp [radialWeight]
  submul k l := by
    have h : 1 + frequencyRadius (k+l) ≤ (1+frequencyRadius k)*(1+frequencyRadius l) := by
      have hp := mul_nonneg (frequencyRadius_nonneg k) (frequencyRadius_nonneg l)
      have ht := frequencyRadius_add_le k l
      nlinarith
    unfold radialWeight
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [frequencyRadius_nonneg (k+l)]) h m

def RadialSummable {d : ℕ} (a : Frequency d → ℂ) (m : ℕ) : Prop :=
  Summable (fun k => radialWeight m k * ‖a k‖)

theorem radialSummable_zero {d : ℕ} (a : Frequency d → ℂ) :
    RadialSummable a 0 ↔ Summable (fun k => ‖a k‖) := by
  simp [RadialSummable, radialWeight]

theorem radialSummable_mono {d : ℕ} {a : Frequency d → ℂ} {m n : ℕ}
    (h : m ≤ n) (ha : RadialSummable a n) : RadialSummable a m := by
  apply ha.of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
  intro k
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by linarith [frequencyRadius_nonneg k]) h) (norm_nonneg _)

theorem exponential_radialSummable {d : ℕ} (a : Frequency d → ℂ) (m : ℕ)
    (ha : RadialSummable a m) : RadialSummable (exponentialCoefficients a) m :=
  exponential_summable (radialWeight_isWeight m) a ha

theorem gibbs_radialSummable {d : ℕ} (u : TorusL2 d) (m : ℕ)
    (hu : RadialSummable (fourierIsometry d u) m)
    (hr : SubcriticalAttainment.RealPotential u) (Z : ℝ) :
    RadialSummable (densityFourier (fun x => Real.exp (u x).re / Z)) m := by
  have hu0 := summable_norm (radialWeight_isWeight m) hu
  have h := (exponential_radialSummable (fourierIsometry d u) m hu).div_const ‖(Z : ℂ)‖
  simpa only [RadialSummable, normalized_real_exp_coefficient u hu0 hr, norm_div,
    ← mul_div_assoc] using h

theorem elliptic_step {d : ℕ} {a b : Frequency d → ℂ} {c : ℝ} (hc : 0 < c)
    (ha0 : a 0 = 0)
    (he : ∀ k, k ≠ 0 → b k = ((c * frequencyRadius k^d : ℝ) : ℂ) * a k)
    (m : ℕ) (hb : RadialSummable b m) : RadialSummable a (m+d) := by
  have hmajor := hb.mul_left ((2:ℝ)^d/c)
  apply hmajor.of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight (m+d)).nonneg k) (norm_nonneg _))
  intro k
  by_cases hk : k = 0
  · simp only [hk, ha0, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (mul_nonneg ((radialWeight_isWeight m).nonneg 0) (norm_nonneg _))
  · have hr := radius_one_le hk
    have hr0 := frequencyRadius_nonneg k
    have hp : (1+frequencyRadius k)^d ≤ (2:ℝ)^d * frequencyRadius k^d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) d
    have hnorm : ‖b k‖ = c * frequencyRadius k^d * ‖a k‖ := by
      rw [he k hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    change (1+frequencyRadius k)^(m+d)*‖a k‖ ≤
      ((2:ℝ)^d/c)*((1+frequencyRadius k)^m*‖b k‖)
    rw [hnorm, pow_add]
    calc
      _ ≤ ((1+frequencyRadius k)^m*((2:ℝ)^d*frequencyRadius k^d))*‖a k‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (norm_nonneg _)
      _ = _ := by field_simp

#print axioms radialWeight_isWeight
#print axioms gibbs_radialSummable
#print axioms elliptic_step

end Legacy.BecknerOnofri.RadialWiener
