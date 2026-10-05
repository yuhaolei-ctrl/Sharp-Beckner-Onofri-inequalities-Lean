import Legacy.TorusEndpoint.GreenKernelReal

/-!
# Absolutely convergent Green pairings and a test-function lower-bound criterion

The pairings use the actual Haar-L² Green function. The final criterion is
explicitly conditional; a uniform Green lower bound is not asserted here.
-/

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace Legacy.TorusEndpoint.GreenPairing

open GreenMultiplierSummability GreenKernelReal

theorem summable_green_pairing_norm {d : ℕ} (f : Lp ℂ 2 (torusMeasure d)) :
    Summable (fun k : Frequency d =>
      ‖(greenMultiplier d k : ℂ) * UnitAddTorus.mFourierCoeff f k‖) := by
  have hsq : Summable (fun k : Frequency d => ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) :=
    (UnitAddTorus.hasSum_sq_mFourierCoeff f).summable
  have hs := ((summable_greenMultiplier_sq d).add hsq).div_const 2
  apply hs.of_nonneg_of_le (fun k => norm_nonneg _)
  intro k
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := sq_nonneg (|greenMultiplier d k| - ‖UnitAddTorus.mFourierCoeff f k‖)
  have he := sq_abs (greenMultiplier d k)
  change |greenMultiplier d k| * ‖UnitAddTorus.mFourierCoeff f k‖ ≤
    (greenMultiplier d k ^ 2 + ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) / 2
  nlinarith

theorem hasSum_green_pairing {d : ℕ} (f : Lp ℂ 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d =>
      (greenMultiplier d k : ℂ) * UnitAddTorus.mFourierCoeff f k)
      (∫ x, conj (greenL2 d x) * f x ∂torusMeasure d) := by
  have h : HasSum (fun k : Frequency d =>
      conj (UnitAddTorus.mFourierCoeff (greenL2 d) k) * UnitAddTorus.mFourierCoeff f k)
      (∫ x, conj (greenL2 d x) * f x ∂torusMeasure d) :=
    UnitAddTorus.hasSum_prod_mFourierCoeff (greenL2 d) f
  simpa only [greenL2_fourierCoeff, Complex.conj_ofReal] using h

theorem fourierCoeff_real_toLp {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (hf.ofReal.toLp (fun x => (f x : ℂ))) k =
      densityFourier f k := by
  unfold UnitAddTorus.mFourierCoeff densityFourier
  apply integral_congr_ae
  have hfc : MemLp (fun x => (f x : ℂ)) 2 (torusMeasure d) := hf.ofReal
  have he : hfc.toLp (fun x => (f x : ℂ)) =ᵐ[torusMeasure d] (fun x => (f x : ℂ)) :=
    hfc.coeFn_toLp
  filter_upwards [he] with x hx
  change UnitAddTorus.mFourier (-k) x * _ = UnitAddTorus.mFourier (-k) x * _
  rw [hx]

theorem summable_realGreen_pairing_norm {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    Summable (fun k : Frequency d =>
      ‖(greenMultiplier d k : ℂ) * densityFourier f k‖) := by
  simpa only [fourierCoeff_real_toLp hf] using
    summable_green_pairing_norm (hf.ofReal.toLp (fun x => (f x : ℂ)))

theorem hasSum_realGreen_pairing {d : ℕ} {f : Torus d → ℝ}
    (hf : MemLp f 2 (torusMeasure d)) :
    HasSum (fun k : Frequency d => greenMultiplier d k * (densityFourier f k).re)
      (∫ x, realGreen d x * f x ∂torusMeasure d) := by
  let F : Lp ℂ 2 (torusMeasure d) := hf.ofReal.toLp (fun x => (f x : ℂ))
  have h := Complex.hasSum_re (hasSum_green_pairing F)
  have hint : Integrable (fun x => conj (greenL2 d x) * F x) (torusMeasure d) :=
    (Lp.memLp (greenL2 d)).star.integrable_mul (Lp.memLp F)
  have he : (∫ x, conj (greenL2 d x) * F x ∂torusMeasure d).re =
      ∫ x, realGreen d x * f x ∂torusMeasure d := by
    calc
      _ = ∫ x, (conj (greenL2 d x) * F x).re ∂torusMeasure d := (integral_re hint).symm
      _ = _ := by
        apply integral_congr_ae
        have hfc : MemLp (fun x => (f x : ℂ)) 2 (torusMeasure d) := hf.ofReal
        have hF : F =ᵐ[torusMeasure d] (fun x => (f x : ℂ)) := hfc.coeFn_toLp
        filter_upwards [realGreen_coe_ae d, hF] with x hg hx
        change F x = (f x : ℂ) at hx
        rw [← hg, hx, Complex.conj_ofReal]
        simp
  rw [he] at h
  simpa only [F, fourierCoeff_real_toLp hf, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using h

/-- Testing against all nonnegative L² functions detects an almost-everywhere
lower bound. This criterion does not assume that the tested function is continuous. -/
theorem ae_lower_bound_of_L2_tests {d : ℕ} {g : Torus d → ℝ}
    (hg : MemLp g 2 (torusMeasure d)) (C : ℝ)
    (htest : ∀ f : Torus d → ℝ, MemLp f 2 (torusMeasure d) →
      (∀ᵐ x ∂torusMeasure d, 0 ≤ f x) →
      -(C * ∫ x, f x ∂torusMeasure d) ≤ ∫ x, g x * f x ∂torusMeasure d) :
    ∀ᵐ x ∂torusMeasure d, -C ≤ g x := by
  let f : Torus d → ℝ := fun x => max (-(g x + C)) 0
  have hf : MemLp f 2 (torusMeasure d) := (hg.add (memLp_const C)).neg.pos_part
  have hfp : ∀ x, 0 ≤ f x := fun x => le_max_right _ _
  have ht := htest f hf (Eventually.of_forall hfp)
  have hi : (∫ x, (g x + C) * f x ∂torusMeasure d) =
      (∫ x, g x * f x ∂torusMeasure d) + C * ∫ x, f x ∂torusMeasure d := by
    simp_rw [add_mul]
    have hgf : Integrable (fun x => g x * f x) (torusMeasure d) := hg.integrable_mul hf
    have hCf : Integrable (fun x => C * f x) (torusMeasure d) :=
      (hf.integrable (by norm_num)).const_mul C
    rw [integral_add hgf hCf, integral_const_mul]
  have he (x) : (g x + C) * f x = -(f x ^ 2) := by
    dsimp [f]
    by_cases hh : 0 ≤ -(g x + C)
    · rw [max_eq_left hh]
      ring
    · rw [max_eq_right (le_of_not_ge hh)]
      ring
  have hs : (∫ x, f x ^ 2 ∂torusMeasure d) = 0 := by
    have hn : 0 ≤ ∫ x, f x ^ 2 ∂torusMeasure d := integral_nonneg (fun x => sq_nonneg _)
    simp_rw [he] at hi
    rw [integral_neg] at hi
    linarith
  have hz : ∀ᵐ x ∂torusMeasure d, f x ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hf.integrable_sq).mp hs
  filter_upwards [hz] with x hx
  have hh : f x = 0 := sq_eq_zero_iff.mp hx
  have hle : -(g x + C) ≤ f x := le_max_left _ _
  linarith

end Legacy.TorusEndpoint.GreenPairing
