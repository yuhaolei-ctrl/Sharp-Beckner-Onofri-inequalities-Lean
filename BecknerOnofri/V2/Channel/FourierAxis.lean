module

public import BecknerOnofri.Definitions
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-!
# Axis Fourier coefficients of a coordinatewise-even density (work package G10)

For a continuous density `f` on `𝕋^d` with `f(-x) = f(x)`:
* `fourierCoeff_even_im`: every Fourier coefficient is real;
* `fourierCoeff_axis_re`: `Re f̂(n e_i) = ∫ f(x) cos(2π n x_i) dm(x)`;
* `fourierCoeff_axis_norm_sq`: `|f̂(n e_i)|² = (∫ f cos(2π n x_i))²`.
-/
noncomputable section
open MeasureTheory
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim

instance torusMeasure_isNegInvariant (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  unfold torusMeasure
  exact MeasureTheory.Measure.pi.isNegInvariant (fun _ => AddCircle.haarAddCircle)

theorem mFourier_neg_point {d : ℕ} (k : Frequency d) (x : Torus d) :
    UnitAddTorus.mFourier k (-x) = UnitAddTorus.mFourier (-k) x := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply]
  apply Finset.prod_congr rfl
  intro i _
  simp [AddCircle.toCircle_neg]

/-- Every Fourier coefficient of a continuous function with `f(-x) = f(x)` is real. -/
theorem fourierCoeff_even_im {d : ℕ} {f : Torus d → ℝ} (heven : ∀ x, f (-x) = f x)
    (k : Frequency d) : (HighDim.fourierCoeff f k).im = 0 := by
  have hc : (starRingEnd ℂ) (HighDim.fourierCoeff f k) = HighDim.fourierCoeff f k := by
    unfold HighDim.fourierCoeff
    rw [← integral_conj]
    have h1 : (fun x => (starRingEnd ℂ) (UnitAddTorus.mFourier (-k) x * (f x : ℂ))) =
        fun x => UnitAddTorus.mFourier k x * (f x : ℂ) := by
      funext x
      rw [map_mul, ← UnitAddTorus.mFourier_neg, neg_neg, Complex.conj_ofReal]
    rw [h1]
    rw [← integral_neg_eq_self (fun x => UnitAddTorus.mFourier k x * (f x : ℂ)) (torusMeasure d)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [mFourier_neg_point, heven]
  exact Complex.conj_eq_iff_im.mp hc

theorem fourierCoeff_axis_re {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f) (i : Fin d) (n : ℤ) :
    (HighDim.fourierCoeff f (Pi.single i n)).re =
      ∫ x, f x * (fourier n (x i)).re ∂torusMeasure d := by
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-Pi.single i n) x * (f x : ℂ))
      (torusMeasure d) :=
    ((UnitAddTorus.mFourier _).continuous.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold HighDim.fourierCoeff
  have hre := integral_re hi
  change (∫ x, (UnitAddTorus.mFourier (-Pi.single i n) x * (f x : ℂ)).re ∂torusMeasure d) =
    (∫ x, UnitAddTorus.mFourier (-Pi.single i n) x * (f x : ℂ) ∂torusMeasure d).re at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [] with x
  have hchar (k : ℤ) : UnitAddTorus.mFourier (Pi.single i k) x = fourier k (x i) := by
    classical
    change (∏ j, fourier ((Pi.single i k : Frequency d) j) (x j)) = _
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  rw [← Pi.single_neg, hchar, fourier_neg]
  simp [Complex.mul_re, mul_comm]

theorem fourierCoeff_axis_norm_sq {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f)
    (heven : ∀ x, f (-x) = f x) (i : Fin d) (n : ℤ) :
    ‖HighDim.fourierCoeff f (Pi.single i n)‖ ^ 2 =
      (∫ x, f x * (fourier n (x i)).re ∂torusMeasure d) ^ 2 := by
  have h := Complex.sq_norm_sub_sq_im (HighDim.fourierCoeff f (Pi.single i n))
  simpa only [fourierCoeff_even_im heven, zero_pow (by decide : 2 ≠ 0), sub_zero,
    fourierCoeff_axis_re hf] using h

end BecknerOnofri.V2.Channel
