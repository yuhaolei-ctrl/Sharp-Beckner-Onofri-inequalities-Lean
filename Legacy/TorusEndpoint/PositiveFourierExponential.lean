import Legacy.TorusEndpoint.PositiveFourierSeries
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponentiation preserves nonnegative absolutely summable Fourier coefficients

The coefficients are defined by iterated actual convolution and their Taylor
sum. The total coefficient mass is exactly the exponential of the input mass.
-/

open scoped BigOperators

namespace Legacy.TorusEndpoint

set_option maxHeartbeats 800000

noncomputable def fourierPower {d : ℕ} (a : Frequency d → ℝ) :
    ℕ → Frequency d → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => fourierConvolution (fourierPower a n) a

theorem fourierPower_nonneg {d : ℕ} (a : Frequency d → ℝ)
    (ha : ∀ k, 0 ≤ a k) (n : ℕ) (k) : 0 ≤ fourierPower a n k := by
  induction n generalizing k with
  | zero => simp only [fourierPower]; split_ifs <;> positivity
  | succ n ih => exact fourierConvolution_nonneg _ _ ih ha k

theorem fourierPower_hasSum {d : ℕ} (a : Frequency d → ℝ)
    (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) (n : ℕ) :
    HasSum (fourierPower a n) ((∑' k, a k) ^ n) := by
  classical
  induction n with
  | zero => simpa only [fourierPower, pow_zero] using hasSum_ite_eq (0 : Frequency d) (1 : ℝ)
  | succ n ih =>
    simpa only [fourierPower, ih.tsum_eq, pow_succ] using
      fourierConvolution_hasSum (fourierPower a n) a ih.summable ha
        (fourierPower_nonneg a hpos n) hpos

theorem fourierPower_series {d : ℕ} (a : Frequency d → ℝ)
    (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) (n : ℕ) (x : Torus d) :
    absoluteFourierSeries (fun k => (fourierPower a n k : ℂ)) x =
      absoluteFourierSeries (fun k => (a k : ℂ)) x ^ n := by
  classical
  induction n with
  | zero => simp [fourierPower, absoluteFourierSeries, apply_ite, ite_mul,
      UnitAddTorus.mFourier_zero]
  | succ n ih =>
    rw [fourierPower, fourierConvolution_series _ _
      (fourierPower_hasSum a ha hpos n).summable ha
      (fourierPower_nonneg a hpos n) hpos, ih, pow_succ]

noncomputable def fourierExponential {d : ℕ} (a : Frequency d → ℝ)
    (k : Frequency d) : ℝ :=
  ∑' n : ℕ, (n.factorial : ℝ)⁻¹ * fourierPower a n k

theorem fourierExponential_nonneg {d : ℕ} (a : Frequency d → ℝ)
    (hpos : ∀ k, 0 ≤ a k) (k) : 0 ≤ fourierExponential a k := by
  apply tsum_nonneg
  intro n
  exact mul_nonneg (by positivity) (fourierPower_nonneg a hpos n k)

theorem fourierExponential_joint_summable {d : ℕ} (a : Frequency d → ℝ)
    (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) :
    Summable (fun p : ℕ × Frequency d =>
      (p.1.factorial : ℝ)⁻¹ * fourierPower a p.1 p.2) := by
  apply (summable_prod_of_nonneg (fun p =>
    mul_nonneg (by positivity) (fourierPower_nonneg a hpos p.1 p.2))).mpr
  constructor
  · intro n
    exact (fourierPower_hasSum a ha hpos n).summable.mul_left ((n.factorial : ℝ)⁻¹)
  · have he := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (∑' k, a k)
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ,
      (fourierPower_hasSum a ha hpos _).summable.tsum_mul_left,
      (fourierPower_hasSum a ha hpos _).tsum_eq] using he.summable

theorem fourierExponential_hasSum {d : ℕ} (a : Frequency d → ℝ)
    (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) :
    HasSum (fourierExponential a) (Real.exp (∑' k, a k)) := by
  have hs := fourierExponential_joint_summable a ha hpos
  have he : HasSum (fun n : ℕ => (n.factorial : ℝ)⁻¹ * (∑' k, a k) ^ n)
      (Real.exp (∑' k, a k)) := by
    simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (∑' k, a k)
  have hmass : (∑' p : ℕ × Frequency d,
      (p.1.factorial : ℝ)⁻¹ * fourierPower a p.1 p.2) = Real.exp (∑' k, a k) := by
    rw [hs.tsum_prod]
    simpa only [(fourierPower_hasSum a ha hpos _).summable.tsum_mul_left,
      (fourierPower_hasSum a ha hpos _).tsum_eq] using he.tsum_eq
  have hsum : Summable (fourierExponential a) := hs.prod_symm.prod
  apply hsum.hasSum_iff.mpr
  change (∑' k, ∑' n : ℕ, (n.factorial : ℝ)⁻¹ * fourierPower a n k) = _
  rw [hs.tsum_comm, ← hs.tsum_prod, hmass]

theorem fourierExponential_series {d : ℕ} (a : Frequency d → ℝ)
    (ha : Summable a) (hpos : ∀ k, 0 ≤ a k) (x : Torus d) :
    absoluteFourierSeries (fun k => (fourierExponential a k : ℂ)) x =
      Complex.exp (absoluteFourierSeries (fun k => (a k : ℂ)) x) := by
  have hs := fourierExponential_joint_summable a ha hpos
  have hj : Summable (fun p : ℕ × Frequency d =>
      (((p.1.factorial : ℝ)⁻¹ * fourierPower a p.1 p.2 : ℝ) : ℂ) *
        UnitAddTorus.mFourier p.2 x) := by
    apply hs.of_norm_bounded
    intro p
    have hp : 0 ≤ (p.1.factorial : ℝ)⁻¹ * fourierPower a p.1 p.2 :=
      mul_nonneg (by positivity) (fourierPower_nonneg a hpos p.1 p.2)
    rw [norm_mul, mFourier_norm_apply, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hp]
  have he : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ *
      absoluteFourierSeries (fun k => (a k : ℂ)) x ^ n)
      (Complex.exp (absoluteFourierSeries (fun k => (a k : ℂ)) x)) := by
    simpa only [smul_eq_mul, ← Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
        (absoluteFourierSeries (fun k => (a k : ℂ)) x)
  calc
    _ = ∑' k, ∑' n : ℕ,
        (((n.factorial : ℝ)⁻¹ * fourierPower a n k : ℝ) : ℂ) *
          UnitAddTorus.mFourier k x := by
      simp only [absoluteFourierSeries, fourierExponential,
        Complex.ofReal_tsum, tsum_mul_right]
    _ = ∑' n : ℕ, ∑' k,
        (((n.factorial : ℝ)⁻¹ * fourierPower a n k : ℝ) : ℂ) *
          UnitAddTorus.mFourier k x := hj.tsum_comm
    _ = ∑' n : ℕ, (n.factorial : ℂ)⁻¹ *
        absoluteFourierSeries (fun k => (a k : ℂ)) x ^ n := by
      apply tsum_congr
      intro n
      simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
        mul_assoc, tsum_mul_left]
      rw [← fourierPower_series a ha hpos n x]
      rfl
    _ = _ := he.tsum_eq

end Legacy.TorusEndpoint
