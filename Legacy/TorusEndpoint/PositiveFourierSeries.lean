import Legacy.TorusEndpoint.GridAliasing
import Legacy.TorusEndpoint.ScalarExponentialCoefficients
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Nonnegative absolutely summable Fourier series

The coefficients below are constructed by summing actual frequency fibers.
In particular, their nonnegativity and absolute summability are conclusions,
not assumptions about the exponential of a Fourier series.
-/

open scoped BigOperators

namespace Legacy.TorusEndpoint

noncomputable def groupedFourierCoefficients {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (v : ι → Frequency d) (k : Frequency d) : ℝ :=
  ∑' i : v ⁻¹' {k}, a i

theorem groupedFourierCoefficients_nonneg {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (v : ι → Frequency d) (ha : ∀ i, 0 ≤ a i) (k) :
    0 ≤ groupedFourierCoefficients a v k :=
  tsum_nonneg (fun _ => ha _)

theorem groupedFourierCoefficients_hasSum {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (v : ι → Frequency d) (ha : Summable a) :
    HasSum (groupedFourierCoefficients a v) (∑' i, a i) :=
  ha.hasSum.tsum_fiberwise v

theorem groupedFourierCoefficients_series {d : ℕ} {ι : Type*}
    (a : ι → ℝ) (v : ι → Frequency d)
    (ha : Summable a) (hpos : ∀ i, 0 ≤ a i) (x : Torus d) :
    absoluteFourierSeries (fun k => (groupedFourierCoefficients a v k : ℂ)) x =
      ∑' i, (a i : ℂ) * UnitAddTorus.mFourier (v i) x := by
  have hs : Summable (fun i => (a i : ℂ) * UnitAddTorus.mFourier (v i) x) := by
    apply ha.of_norm_bounded
    intro i
    simp [norm_mul, mFourier_norm_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpos i)]
  have h := hs.hasSum.tsum_fiberwise v
  have heq (k : Frequency d) :
      (∑' i : v ⁻¹' {k}, (a i : ℂ) * UnitAddTorus.mFourier (v i) x) =
        (groupedFourierCoefficients a v k : ℂ) * UnitAddTorus.mFourier k x := by
    have hsub : Summable (fun i : v ⁻¹' {k} => a i) := ha.subtype _
    calc
      _ = ∑' i : v ⁻¹' {k}, (a i : ℂ) * UnitAddTorus.mFourier k x := by
        apply tsum_congr
        intro i
        rw [show v i = k from i.property]
      _ = (∑' i : v ⁻¹' {k}, (a i : ℂ)) * UnitAddTorus.mFourier k x :=
        (Complex.hasSum_ofReal.mpr hsub.hasSum).summable.tsum_mul_right _
      _ = _ := by rw [(Complex.hasSum_ofReal.mpr hsub.hasSum).tsum_eq]; rfl
  simpa only [heq, absoluteFourierSeries] using h.tsum_eq

noncomputable def fourierConvolution {d : ℕ} (a b : Frequency d → ℝ) :
    Frequency d → ℝ :=
  groupedFourierCoefficients (fun p : Frequency d × Frequency d => a p.1 * b p.2)
    (fun p => p.1 + p.2)

theorem fourierConvolution_nonneg {d : ℕ} (a b : Frequency d → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (k) :
    0 ≤ fourierConvolution a b k := by
  unfold fourierConvolution
  exact groupedFourierCoefficients_nonneg
    (fun p : Frequency d × Frequency d => a p.1 * b p.2)
    (fun p => p.1 + p.2) (fun p => mul_nonneg (ha p.1) (hb p.2)) k

theorem fourierConvolution_hasSum {d : ℕ} (a b : Frequency d → ℝ)
    (ha : Summable a) (hb : Summable b)
    (hpa : ∀ k, 0 ≤ a k) (hpb : ∀ k, 0 ≤ b k) :
    HasSum (fourierConvolution a b) ((∑' k, a k) * ∑' k, b k) := by
  have hs := ha.mul_of_nonneg hb hpa hpb
  unfold fourierConvolution
  simpa only [← ha.tsum_mul_tsum hb hs] using
    groupedFourierCoefficients_hasSum _ (fun p => p.1 + p.2) hs

theorem fourierConvolution_series {d : ℕ} (a b : Frequency d → ℝ)
    (ha : Summable a) (hb : Summable b)
    (hpa : ∀ k, 0 ≤ a k) (hpb : ∀ k, 0 ≤ b k) (x : Torus d) :
    absoluteFourierSeries (fun k => (fourierConvolution a b k : ℂ)) x =
      absoluteFourierSeries (fun k => (a k : ℂ)) x *
        absoluteFourierSeries (fun k => (b k : ℂ)) x := by
  rw [fourierConvolution, groupedFourierCoefficients_series _ _
    (ha.mul_of_nonneg hb hpa hpb) (fun p => mul_nonneg (hpa p.1) (hpb p.2))]
  have hna : Summable (fun k => ‖(a k : ℂ) * UnitAddTorus.mFourier k x‖) := by
    simpa [norm_mul, mFourier_norm_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpa _)] using ha
  have hnb : Summable (fun k => ‖(b k : ℂ) * UnitAddTorus.mFourier k x‖) := by
    simpa [norm_mul, mFourier_norm_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hpb _)] using hb
  rw [absoluteFourierSeries, absoluteFourierSeries,
    tsum_mul_tsum_of_summable_norm hna hnb]
  apply tsum_congr
  intro p
  rw [UnitAddTorus.mFourier_add, Complex.ofReal_mul]
  ring

end Legacy.TorusEndpoint
