import Legacy.BecknerOnofri.AngularMixedL2
import Legacy.BecknerOnofri.JacobiTensorSpectrum
import Legacy.BecknerOnofri.SubcriticalWiener

/-! Actual bounded inverse powers intertwine the full angular differentiated
Fourier series. This proves the Euler inverse equation in the real L2 cube. -/
noncomputable section
namespace Legacy.BecknerOnofri.AngularSpectralIntertwining
open Legacy.TorusEndpoint TorusSobolev RadialWiener AngularMixedTerms AngularMixedL2
open JacobiTensor JacobiTensorSpectrum
open scoped BigOperators

theorem countIndex_ne_zero {d : ℕ} (is : List (Fin d)) (his : is ≠ []) : countIndex is ≠ 0 := by
  cases is with
  | nil => exact (his rfl).elim
  | cons i js =>
    intro he
    have h := congrFun he i
    simp [countIndex] at h

theorem frequency_ne_zero {d : ℕ} (is : List (Fin d)) (his : is ≠ []) (k : Frequency d)
    (hk : ∀ i, is.count i ≤ (k i).natAbs) : k ≠ 0 := by
  intro he
  apply countIndex_ne_zero is his
  funext i
  have h := hk i
  rw [he] at h
  simpa [countIndex] using h

theorem shifted_eigenvalue {d : ℕ} (is : List (Fin d)) (k : Frequency d)
    (hk : ∀ i, is.count i ≤ (k i).natAbs) :
    tensorEigenvalue (countIndex is) (shiftedIndex is k) = frequencyRadius k^2 := by
  rw [GreenMultiplierSummability.frequencyRadius_sq]
  unfold tensorEigenvalue GreenMultiplierSummability.radiusSq
  apply Finset.sum_congr rfl
  intro i _
  change (((k i).natAbs-is.count i+is.count i : ℕ) : ℝ)^2 = (k i : ℝ)^2
  rw [Nat.sub_add_cancel (hk i), Nat.cast_natAbs, Int.cast_abs, sq_abs]

theorem critical_multiplier {d : ℕ} (is : List (Fin d)) (k : Frequency d)
    (hk : ∀ i, is.count i ≤ (k i).natAbs) :
    (tensorEigenvalue (countIndex is) (shiftedIndex is k))^(-((d:ℝ)/2)) =
      (frequencyRadius k^d)⁻¹ := by
  rw [shifted_eigenvalue is k hk, ← Real.rpow_natCast (frequencyRadius k) 2,
    ← Real.rpow_mul (frequencyRadius_nonneg k)]
  have he : (2:ℝ)*(-((d:ℝ)/2)) = -(d:ℝ) := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.rpow_neg (frequencyRadius_nonneg k), Real.rpow_natCast]

theorem criticalInverse_tensorVector {d : ℕ} (α : Index d) (hα : α ≠ 0) (n : Index d) :
    criticalInverse α hα (tensorVector α n) =
      (tensorEigenvalue α n)^(-((d:ℝ)/2)) • tensorVector α n := by
  classical
  apply (hilbertBasis α).repr.injective
  ext l
  change (hilbertBasis α).repr (inversePower α hα _ _ (tensorVector α n)) l = _
  rw [repr_inversePower, ← hilbertBasis_apply, map_smul, (hilbertBasis α).repr_self]
  by_cases he : n = l
  · subst l; simp
  · simp [lp.single_apply, he]

theorem term_intertwining {d : ℕ} (a b : Frequency d → ℂ) (c : ℝ)
    (hcoeff : ∀ k : Frequency d, k ≠ 0 →
      a k = ((c*(frequencyRadius k^d)⁻¹ : ℝ) : ℂ)*b k)
    (is : List (Fin d)) (his : is ≠ []) (k : Frequency d) :
    termVector a is k = c • criticalInverse (countIndex is) (countIndex_ne_zero is his)
      (termVector b is k) := by
  by_cases hk : ∀ i, is.count i ≤ (k i).natAbs
  · rw [termVector_eq_tensor a is k hk, termVector_eq_tensor b is k hk,
      map_smul, criticalInverse_tensorVector, smul_smul, smul_smul,
      critical_multiplier is k hk]
    congr 1
    rw [hcoeff k (frequency_ne_zero is his k hk)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · push Not at hk
    obtain ⟨i, hi⟩ := hk
    rw [termVector_eq_zero a is k i hi, termVector_eq_zero b is k i hi, map_zero, smul_zero]

theorem inverse_intertwining {d : ℕ} (a b : Frequency d → ℂ) (c : ℝ)
    (_ha : ∀ m : ℕ, RadialSummable a m) (hb : ∀ m : ℕ, RadialSummable b m)
    (hcoeff : ∀ k : Frequency d, k ≠ 0 →
      a k = ((c*(frequencyRadius k^d)⁻¹ : ℝ) : ℂ)*b k)
    (is : List (Fin d)) (his : is ≠ []) :
    vector a is = c • criticalInverse (countIndex is) (countIndex_ne_zero is his) (vector b is) := by
  rw [vector, vector, (criticalInverse (countIndex is) (countIndex_ne_zero is his)).map_tsum
    (termVector_norm_summable b hb is).of_norm, ← tsum_const_smul'']
  apply tsum_congr
  intro k
  exact term_intertwining a b c hcoeff is his k

open SubcriticalAttainment SubcriticalEuler in
theorem maximizer_inverse_equation {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u)
    (is : List (Fin d)) (his : is ≠ []) :
    vector (fourierIsometry d u) is = (1/(2*A)) •
      criticalInverse (countIndex is) (countIndex_ne_zero is his)
        (vector (densityFourier (gibbsValue u)) is) :=
  inverse_intertwining _ _ _ (maximizer_radialSummable hd hR hA hu hmax)
    (maximizer_density_radialSummable hd hR hA hu hmax)
    (fun _ hk => maximizer_fourier_formula hR hA hu hmax hk) is his

#print axioms inverse_intertwining
#print axioms maximizer_inverse_equation
end Legacy.BecknerOnofri.AngularSpectralIntertwining
