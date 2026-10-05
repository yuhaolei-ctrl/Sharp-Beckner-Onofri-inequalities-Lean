import Legacy.TorusEndpoint.PositiveFourierAnalytic
import Legacy.BecknerOnofri.TorusSobolevCompactness

/-!
# The complex Wiener algebra on the unit torus

All coefficients may be complex.  Absolute summability is proved by comparison
with the nonnegative convolution of their norms; no positivity is required of
the input Fourier coefficients.
-/

open MeasureTheory
open scoped BigOperators

namespace Legacy.BecknerOnofri.WienerFourier

open Legacy.TorusEndpoint TorusSobolev

set_option maxHeartbeats 800000

noncomputable def grouped {d : ℕ} {ι : Type*} (a : ι → ℂ)
    (v : ι → Frequency d) (k : Frequency d) : ℂ :=
  ∑' i : v ⁻¹' {k}, a i

theorem norm_grouped_le {d : ℕ} {ι : Type*} (a : ι → ℂ)
    (v : ι → Frequency d) (ha : Summable (fun i => ‖a i‖)) (k) :
    ‖grouped a v k‖ ≤ groupedFourierCoefficients (fun i => ‖a i‖) v k :=
  norm_tsum_le_tsum_norm (ha.subtype _)

theorem grouped_norm_summable {d : ℕ} {ι : Type*} (a : ι → ℂ)
    (v : ι → Frequency d) (ha : Summable (fun i => ‖a i‖)) :
    Summable (fun k => ‖grouped a v k‖) := by
  apply (groupedFourierCoefficients_hasSum _ v ha).summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact norm_grouped_le a v ha

theorem grouped_series {d : ℕ} {ι : Type*} (a : ι → ℂ)
    (v : ι → Frequency d) (ha : Summable (fun i => ‖a i‖)) (x : Torus d) :
    absoluteFourierSeries (grouped a v) x =
      ∑' i, a i * UnitAddTorus.mFourier (v i) x := by
  have hs : Summable (fun i => a i * UnitAddTorus.mFourier (v i) x) := by
    apply ha.of_norm_bounded
    intro i
    simp only [norm_mul, mFourier_norm_apply, mul_one, le_refl]
  have ht := hs.hasSum.tsum_fiberwise v
  have heq (k : Frequency d) :
      (∑' i : v ⁻¹' {k}, a i * UnitAddTorus.mFourier (v i) x) =
        grouped a v k * UnitAddTorus.mFourier k x := by
    calc
      _ = ∑' i : v ⁻¹' {k}, a i * UnitAddTorus.mFourier k x := by
        apply tsum_congr
        intro i
        rw [show v i = k from i.property]
      _ = _ := tsum_mul_right
  simpa only [heq, absoluteFourierSeries] using ht.tsum_eq

noncomputable def convolution {d : ℕ} (a b : Frequency d → ℂ) : Frequency d → ℂ :=
  grouped (fun p : Frequency d × Frequency d => a p.1 * b p.2)
    (fun p => p.1 + p.2)

theorem convolution_norm_le {d : ℕ} (a b : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖)) (k) :
    ‖convolution a b k‖ ≤ fourierConvolution (fun k => ‖a k‖) (fun k => ‖b k‖) k := by
  have hs := ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  simpa only [convolution, fourierConvolution, norm_mul] using
    norm_grouped_le (fun p : Frequency d × Frequency d => a p.1 * b p.2)
      (fun p => p.1 + p.2) (by simpa only [norm_mul] using hs) k

theorem convolution_norm_summable {d : ℕ} (a b : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖)) :
    Summable (fun k => ‖convolution a b k‖) := by
  apply grouped_norm_summable
  simpa only [norm_mul] using
    ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

theorem convolution_series {d : ℕ} (a b : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (hb : Summable (fun k => ‖b k‖)) (x : Torus d) :
    absoluteFourierSeries (convolution a b) x =
      absoluteFourierSeries a x * absoluteFourierSeries b x := by
  have hs : Summable (fun p : Frequency d × Frequency d => ‖a p.1 * b p.2‖) := by
    simpa only [norm_mul] using
      ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  rw [convolution, grouped_series _ _ hs]
  have hna : Summable (fun k => ‖a k * UnitAddTorus.mFourier k x‖) := by
    simpa only [norm_mul, mFourier_norm_apply, mul_one] using ha
  have hnb : Summable (fun k => ‖b k * UnitAddTorus.mFourier k x‖) := by
    simpa only [norm_mul, mFourier_norm_apply, mul_one] using hb
  rw [absoluteFourierSeries, absoluteFourierSeries,
    tsum_mul_tsum_of_summable_norm hna hnb]
  apply tsum_congr
  intro p
  rw [UnitAddTorus.mFourier_add]
  ring

noncomputable def convolutionPower {d : ℕ} (a : Frequency d → ℂ) :
    ℕ → Frequency d → ℂ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => convolution (convolutionPower a n) a

theorem convolutionPower_norm_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (n) :
    Summable (fun k => ‖convolutionPower a n k‖) := by
  classical
  induction n with
  | zero => simpa only [convolutionPower, apply_ite, norm_one, norm_zero] using
      (hasSum_ite_eq (0 : Frequency d) (1 : ℝ)).summable
  | succ n ih => exact convolution_norm_summable _ _ ih ha

theorem convolutionPower_series {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (n) (x : Torus d) :
    absoluteFourierSeries (convolutionPower a n) x = absoluteFourierSeries a x ^ n := by
  classical
  induction n with
  | zero => simp [convolutionPower, absoluteFourierSeries, ite_mul,
      UnitAddTorus.mFourier_zero]
  | succ n ih =>
    rw [convolutionPower, convolution_series _ _ (convolutionPower_norm_summable a ha n) ha,
      ih, pow_succ]

theorem fourierConvolution_mono_left {d : ℕ} (a b c : Frequency d → ℝ)
    (ha : Summable a) (hb : Summable b) (hc : Summable c)
    (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k) (hc0 : ∀ k, 0 ≤ c k)
    (hab : ∀ k, a k ≤ b k) (k) :
    fourierConvolution a c k ≤ fourierConvolution b c k := by
  apply Summable.tsum_le_tsum
  · intro p
    exact mul_le_mul_of_nonneg_right (hab p.val.1) (hc0 p.val.2)
  · exact (ha.mul_of_nonneg hc ha0 hc0).subtype _
  · exact (hb.mul_of_nonneg hc hb0 hc0).subtype _

theorem convolutionPower_norm_le {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (n k) :
    ‖convolutionPower a n k‖ ≤ fourierPower (fun k => ‖a k‖) n k := by
  classical
  induction n generalizing k with
  | zero => simp only [convolutionPower, fourierPower]; split_ifs <;> norm_num
  | succ n ih =>
    exact (convolution_norm_le _ _ (convolutionPower_norm_summable a ha n) ha k).trans
      (fourierConvolution_mono_left _ _ _
        (convolutionPower_norm_summable a ha n)
        (fourierPower_hasSum _ ha (fun _ => norm_nonneg _) n).summable ha
        (fun _ => norm_nonneg _) (fourierPower_nonneg _ (fun _ => norm_nonneg _) n)
        (fun _ => norm_nonneg _) ih k)

noncomputable def exponentialCoefficients {d : ℕ} (a : Frequency d → ℂ)
    (k : Frequency d) : ℂ :=
  ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * convolutionPower a n k

theorem exponential_joint_norm_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    Summable (fun p : ℕ × Frequency d =>
      ‖(p.1.factorial : ℂ)⁻¹ * convolutionPower a p.1 p.2‖) := by
  apply (fourierExponential_joint_summable (fun k => ‖a k‖) ha
    (fun _ => norm_nonneg _)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (convolutionPower_norm_le a ha p.1 p.2) (by positivity)

theorem exponential_norm_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    Summable (fun k => ‖exponentialCoefficients a k‖) := by
  have hs := exponential_joint_norm_summable a ha
  apply hs.prod_symm.prod.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  exact norm_tsum_le_tsum_norm (hs.prod_symm.prod_factor k)

theorem exponential_norm_sum_le {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    (∑' k, ‖exponentialCoefficients a k‖) ≤ Real.exp (∑' k, ‖a k‖) := by
  have hs := exponential_joint_norm_summable a ha
  have hmajor := fourierExponential_hasSum (fun k => ‖a k‖) ha (fun _ => norm_nonneg _)
  rw [← hmajor.tsum_eq]
  apply Summable.tsum_le_tsum _ (exponential_norm_summable a ha) hmajor.summable
  intro k
  calc
    _ ≤ ∑' n, ‖(n.factorial : ℂ)⁻¹ * convolutionPower a n k‖ :=
      norm_tsum_le_tsum_norm (hs.prod_symm.prod_factor k)
    _ ≤ fourierExponential (fun k => ‖a k‖) k := by
      apply Summable.tsum_le_tsum _ (hs.prod_symm.prod_factor k)
        ((fourierExponential_joint_summable _ ha (fun _ => norm_nonneg _)).prod_symm.prod_factor k)
      intro n
      simp only [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (convolutionPower_norm_le a ha n k) (by positivity)

theorem exponential_series {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (x : Torus d) :
    absoluteFourierSeries (exponentialCoefficients a) x =
      Complex.exp (absoluteFourierSeries a x) := by
  have hs := exponential_joint_norm_summable a ha
  have hj : Summable (fun p : ℕ × Frequency d =>
      ((p.1.factorial : ℂ)⁻¹ * convolutionPower a p.1 p.2) *
        UnitAddTorus.mFourier p.2 x) := by
    apply hs.of_norm_bounded
    intro p
    simp only [norm_mul, mFourier_norm_apply, mul_one, le_refl]
  have he : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * absoluteFourierSeries a x ^ n)
      (Complex.exp (absoluteFourierSeries a x)) := by
    simpa only [smul_eq_mul, ← Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (absoluteFourierSeries a x)
  calc
    _ = ∑' k, ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * convolutionPower a n k) *
        UnitAddTorus.mFourier k x := by
      simp only [absoluteFourierSeries, exponentialCoefficients, tsum_mul_right]
    _ = ∑' n : ℕ, ∑' k, ((n.factorial : ℂ)⁻¹ * convolutionPower a n k) *
        UnitAddTorus.mFourier k x := hj.tsum_comm
    _ = ∑' n : ℕ, (n.factorial : ℂ)⁻¹ * absoluteFourierSeries a x ^ n := by
      apply tsum_congr
      intro n
      simp only [mul_assoc, tsum_mul_left]
      rw [← convolutionPower_series a ha n x]
      rfl
    _ = _ := he.tsum_eq

theorem exponential_coefficient {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (k) :
    UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k =
      exponentialCoefficients a k := by
  have he : (fun x => Complex.exp (absoluteFourierSeries a x)) =
      absoluteFourierSeries (exponentialCoefficients a) :=
    funext (fun x => (exponential_series a ha x).symm)
  rw [he]
  exact absoluteFourierSeries_coefficient _ (exponential_norm_summable a ha) k

theorem exponential_fourier_summable {d : ℕ} (a : Frequency d → ℂ)
    (ha : Summable (fun k => ‖a k‖)) :
    Summable (fun k =>
      ‖UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k‖) := by
  simpa only [exponential_coefficient a ha] using exponential_norm_summable a ha

#print axioms convolution_series
#print axioms exponential_norm_sum_le
#print axioms exponential_series
#print axioms exponential_fourier_summable

end Legacy.BecknerOnofri.WienerFourier
