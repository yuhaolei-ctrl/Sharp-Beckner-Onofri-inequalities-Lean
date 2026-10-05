import Legacy.BecknerOnofri.WienerFourier
import Legacy.BecknerOnofri.SubcriticalAttainmentDefs

/-! Actual continuous representatives for `L²` functions with absolutely
summable Fourier coefficients, and Wiener closure under exponentiation. -/

open MeasureTheory
open scoped BigOperators

namespace Legacy.BecknerOnofri.WienerFourier

open Legacy.TorusEndpoint TorusSobolev

noncomputable def representative {d : ℕ} (u : TorusL2 d) : Torus d → ℂ :=
  absoluteFourierSeries (fourierIsometry d u)

theorem representative_continuous {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) :
    Continuous (representative u) :=
  absoluteFourierSeries_continuous _ hu

theorem fourierCoeff_congr_ae {d : ℕ} {f g : Torus d → ℂ}
    (h : f =ᵐ[torusMeasure d] g) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff f k = UnitAddTorus.mFourierCoeff g k := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem representative_ae_eq {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) :
    representative u =ᵐ[torusMeasure d] u := by
  have hf : MemLp (representative u) 2 (torusMeasure d) :=
    (representative_continuous u hu).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : hf.toLp (representative u) = u := by
    apply (fourierIsometry d).injective
    ext k
    rw [fourierIsometry_apply]
    calc
      UnitAddTorus.mFourierCoeff (hf.toLp (representative u)) k =
          UnitAddTorus.mFourierCoeff (representative u) k :=
        fourierCoeff_congr_ae hf.coeFn_toLp k
      _ = fourierIsometry d u k := absoluteFourierSeries_coefficient _ hu k
  exact hf.coeFn_toLp.symm.trans (by rw [he])

theorem representative_coefficient {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) (k) :
    UnitAddTorus.mFourierCoeff (representative u) k = fourierIsometry d u k :=
  absoluteFourierSeries_coefficient _ hu k

theorem representative_real {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖))
    (hr : SubcriticalAttainment.RealPotential u) (x : Torus d) :
    (representative u x).im = 0 := by
  have he : (fun x => (representative u x).im) =ᵐ[torusMeasure d] (fun _ => (0 : ℝ)) := by
    filter_upwards [representative_ae_eq u hu, hr] with x hx hrx
    rw [hx, hrx]
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    rw [torusMeasure_explicit]
    infer_instance
  have hh := MeasureTheory.Measure.eq_of_ae_eq he
    (Complex.continuous_im.comp (representative_continuous u hu)) continuous_const
  exact congrFun hh x

theorem exp_fourier_coefficient {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) (k : Frequency d) :
    UnitAddTorus.mFourierCoeff (fun x => Complex.exp (u x)) k =
      exponentialCoefficients (fourierIsometry d u) k := by
  calc
    _ = UnitAddTorus.mFourierCoeff (fun x => Complex.exp (representative u x)) k := by
      apply fourierCoeff_congr_ae
      filter_upwards [representative_ae_eq u hu] with x hx
      rw [hx]
    _ = _ := exponential_coefficient _ hu k

theorem exp_fourier_summable {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖)) :
    Summable (fun k => ‖UnitAddTorus.mFourierCoeff (fun x => Complex.exp (u x)) k‖) := by
  simpa only [exp_fourier_coefficient u hu] using
    exponential_norm_summable (fourierIsometry d u) hu

theorem real_exp_coefficient {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖))
    (hr : SubcriticalAttainment.RealPotential u) (k : Frequency d) :
    densityFourier (fun x => Real.exp (u x).re) k =
      exponentialCoefficients (fourierIsometry d u) k := by
  calc
    _ = UnitAddTorus.mFourierCoeff (fun x => Complex.exp (u x)) k := by
      change UnitAddTorus.mFourierCoeff (fun x => (Real.exp (u x).re : ℂ)) k = _
      apply fourierCoeff_congr_ae
      filter_upwards [hr] with x hx
      rw [Complex.ofReal_exp]
      congr 1
      apply Complex.ext <;> simp [hx]
    _ = _ := exp_fourier_coefficient u hu k

theorem real_exp_fourier_summable {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖))
    (hr : SubcriticalAttainment.RealPotential u) :
    Summable (fun k => ‖densityFourier (fun x => Real.exp (u x).re) k‖) := by
  simpa only [real_exp_coefficient u hu hr] using
    exponential_norm_summable (fourierIsometry d u) hu

theorem normalized_real_exp_coefficient {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖))
    (hr : SubcriticalAttainment.RealPotential u) (Z : ℝ) (k : Frequency d) :
    densityFourier (fun x => Real.exp (u x).re / Z) k =
      exponentialCoefficients (fourierIsometry d u) k / (Z : ℂ) := by
  calc
    _ = densityFourier (fun x => Real.exp (u x).re) k / (Z : ℂ) := by
      simp only [densityFourier, Complex.ofReal_div, ← mul_div_assoc, integral_div]
    _ = _ := by rw [real_exp_coefficient u hu hr]

theorem normalized_real_exp_fourier_summable {d : ℕ} (u : TorusL2 d)
    (hu : Summable (fun k => ‖fourierIsometry d u k‖))
    (hr : SubcriticalAttainment.RealPotential u) (Z : ℝ) :
    Summable (fun k => ‖densityFourier (fun x => Real.exp (u x).re / Z) k‖) := by
  simpa only [normalized_real_exp_coefficient u hu hr, norm_div] using
    (exponential_norm_summable (fourierIsometry d u) hu).div_const ‖(Z : ℂ)‖

#print axioms representative_ae_eq
#print axioms representative_real
#print axioms exp_fourier_summable
#print axioms normalized_real_exp_fourier_summable

end Legacy.BecknerOnofri.WienerFourier
