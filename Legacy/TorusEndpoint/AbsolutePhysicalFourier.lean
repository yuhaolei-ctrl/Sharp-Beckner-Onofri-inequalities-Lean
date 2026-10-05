module

public import Legacy.TorusEndpoint.PositiveFourierAnalytic
public import Legacy.TorusEndpoint.PhysicalFiniteFourier
public import Legacy.TorusEndpoint.IntegrableSeries

@[expose] public section

/-!
# Physical interactions for absolutely summable Fourier kernels

These are actual product-Haar and iterated interaction integrals for arbitrary
probability densities. No L2 or finite-entropy hypothesis on the density is
needed. The coefficients must be absolutely summable; no such assumption is
made about the critical, unsmoothed Green multiplier.
-/

open MeasureTheory Filter

namespace Legacy.TorusEndpoint.AbsolutePhysicalFourier

open PhysicalFiniteFourier

theorem complexInteraction_norm {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) (xy : Torus d × Torus d) :
    ‖complexInteraction rho k xy‖ = ‖rho.value xy.1‖ * ‖rho.value xy.2‖ := by
  simp only [complexInteraction, norm_mul, mFourier_norm_apply, one_mul, Complex.norm_real]

theorem integral_norm_complexInteraction {d : ℕ} (rho : ProbabilityDensity d)
    (k : Frequency d) :
    (∫ xy, ‖complexInteraction rho k xy‖ ∂(torusMeasure d).prod (torusMeasure d)) = 1 := by
  have hm : (∫ x, ‖rho.value x‖ ∂torusMeasure d) = 1 := by
    calc
      _ = ∫ x, rho.value x ∂torusMeasure d := by
        apply integral_congr_ae
        filter_upwards [rho.nonneg] with x hx
        exact Real.norm_of_nonneg hx
      _ = 1 := rho.mass
  simp_rw [complexInteraction_norm]
  calc
    _ = (∫ x, ‖rho.value x‖ ∂torusMeasure d) *
        (∫ x, ‖rho.value x‖ ∂torusMeasure d) :=
      integral_prod_mul (fun x : Torus d => ‖rho.value x‖) (fun x : Torus d => ‖rho.value x‖)
    _ = 1 := by rw [hm, one_mul]

theorem absoluteInteraction_eq_tsum {d : ℕ} (rho : ProbabilityDensity d)
    (b : Frequency d → ℂ) (xy : Torus d × Torus d) :
    absoluteFourierSeries b (xy.1 - xy.2) * (rho.value xy.1 : ℂ) *
      (rho.value xy.2 : ℂ) = ∑' k, b k * complexInteraction rho k xy := by
  simp only [absoluteFourierSeries, complexInteraction, ← tsum_mul_right]
  apply tsum_congr
  intro k
  ring

theorem absoluteInteraction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (b : Frequency d → ℂ) (hb : Summable (fun k => ‖b k‖)) :
    Integrable (fun xy : Torus d × Torus d =>
      absoluteFourierSeries b (xy.1 - xy.2) * (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ))
      ((torusMeasure d).prod (torusMeasure d)) := by
  have hi (k) := (complexInteraction_integrable rho k).const_mul (b k)
  have hs : Summable (fun k => ∫ xy, ‖b k * complexInteraction rho k xy‖
      ∂(torusMeasure d).prod (torusMeasure d)) := by
    simpa only [norm_mul, integral_const_mul, integral_norm_complexInteraction, mul_one] using hb
  apply (IntegrableSeries.integrable_tsum_of_summable_integral_norm hi hs).congr
  exact Eventually.of_forall (fun xy => (absoluteInteraction_eq_tsum rho b xy).symm)

theorem hasSum_absoluteInteraction {d : ℕ} (rho : ProbabilityDensity d)
    (b : Frequency d → ℂ) (hb : Summable (fun k => ‖b k‖)) :
    HasSum (fun k => b k * (‖densityFourier rho.value k‖ ^ 2 : ℝ))
      (∫ xy : Torus d × Torus d,
        absoluteFourierSeries b (xy.1 - xy.2) * (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ)
        ∂(torusMeasure d).prod (torusMeasure d)) := by
  have hi (k) := (complexInteraction_integrable rho k).const_mul (b k)
  have hs : Summable (fun k => ∫ xy, ‖b k * complexInteraction rho k xy‖
      ∂(torusMeasure d).prod (torusMeasure d)) := by
    simpa only [norm_mul, integral_const_mul, integral_norm_complexInteraction, mul_one] using hb
  have h := hasSum_integral_of_summable_integral_norm hi hs
  have he : (∫ xy, (∑' k, b k * complexInteraction rho k xy)
      ∂(torusMeasure d).prod (torusMeasure d)) =
      ∫ xy : Torus d × Torus d,
        absoluteFourierSeries b (xy.1 - xy.2) * (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ)
        ∂(torusMeasure d).prod (torusMeasure d) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun xy => (absoluteInteraction_eq_tsum rho b xy).symm)
  rw [he] at h
  simpa only [integral_const_mul, complexInteraction_integral] using h

noncomputable def realAbsoluteKernel {d : ℕ} (b : Frequency d → ℝ) (x : Torus d) : ℝ :=
  (absoluteFourierSeries (fun k => (b k : ℂ)) x).re

theorem realAbsoluteKernel_interaction_integrable {d : ℕ} (rho : ProbabilityDensity d)
    (b : Frequency d → ℝ) (hb : Summable (fun k => ‖b k‖)) :
    Integrable (fun xy : Torus d × Torus d =>
      realAbsoluteKernel b (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) := by
  have hc : Summable (fun k => ‖(b k : ℂ)‖) := by simpa only [Complex.norm_real] using hb
  have hi : Integrable (fun xy : Torus d × Torus d =>
      (absoluteFourierSeries (fun k => (b k : ℂ)) (xy.1 - xy.2) *
        (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ)).re)
      ((torusMeasure d).prod (torusMeasure d)) :=
    (absoluteInteraction_integrable rho _ hc).re
  simpa only [realAbsoluteKernel, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using hi

theorem hasSum_realAbsoluteKernel_interaction {d : ℕ} (rho : ProbabilityDensity d)
    (b : Frequency d → ℝ) (hb : Summable (fun k => ‖b k‖)) :
    HasSum (fun k => b k * ‖densityFourier rho.value k‖ ^ 2)
      (∫ xy : Torus d × Torus d,
        realAbsoluteKernel b (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2
        ∂(torusMeasure d).prod (torusMeasure d)) := by
  have hc : Summable (fun k => ‖(b k : ℂ)‖) := by simpa only [Complex.norm_real] using hb
  have h := Complex.hasSum_re (hasSum_absoluteInteraction rho _ hc)
  have he : (∫ xy : Torus d × Torus d,
      absoluteFourierSeries (fun k => (b k : ℂ)) (xy.1 - xy.2) *
        (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ)
      ∂(torusMeasure d).prod (torusMeasure d)).re =
      ∫ xy : Torus d × Torus d,
        (absoluteFourierSeries (fun k => (b k : ℂ)) (xy.1 - xy.2) *
          (rho.value xy.1 : ℂ) * (rho.value xy.2 : ℂ)).re
        ∂(torusMeasure d).prod (torusMeasure d) :=
    (integral_re (absoluteInteraction_integrable rho _ hc)).symm
  rw [he] at h
  simpa only [realAbsoluteKernel, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] using h

theorem realAbsoluteKernel_energy_eq_series {d : ℕ} (rho : ProbabilityDensity d)
    (b : Frequency d → ℝ) (hb : Summable (fun k => ‖b k‖)) :
    (∫ x, ∫ y, realAbsoluteKernel b (x - y) * rho.value x * rho.value y
      ∂torusMeasure d ∂torusMeasure d) = ∑' k, b k * ‖densityFourier rho.value k‖ ^ 2 := by
  rw [← integral_prod _ (realAbsoluteKernel_interaction_integrable rho b hb)]
  exact (hasSum_realAbsoluteKernel_interaction rho b hb).tsum_eq.symm

end Legacy.TorusEndpoint.AbsolutePhysicalFourier
