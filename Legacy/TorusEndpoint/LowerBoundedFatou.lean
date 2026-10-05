import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Legacy.TorusEndpoint.PhysicalFiniteFourier

/-!
# Fatou with an integrable lower bound and finite upper integrals

The limit's integrability is a conclusion, not a hypothesis. The measure
need not be finite or a probability measure. No singular kernel is identified
by this abstract theorem.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Legacy.TorusEndpoint.LowerBoundedFatou

set_option maxHeartbeats 800000

theorem integrable_and_integral_le_of_lower_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : ℕ → X → ℝ) (f h : X → ℝ) (B : ℝ)
    (hF : ∀ n, Integrable (F n) μ) (hh : Integrable h μ)
    (hlower : ∀ n, ∀ᵐ x ∂μ, h x ≤ F n x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, (∫ x, F n x ∂μ) ≤ B) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hF n).aestronglyMeasurable) hlim
  have hnonneg (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ F n x - h x := by
    filter_upwards [hlower n] with x hx using sub_nonneg.mpr hx
  have hfl : ∀ᵐ x ∂μ, h x ≤ f x := by
    filter_upwards [ae_all_iff.mpr hlower, hlim] with x hx hxl
    exact ge_of_tendsto hxl (Eventually.of_forall hx)
  have hfn : ∀ᵐ x ∂μ, 0 ≤ f x - h x := by
    filter_upwards [hfl] with x hx using sub_nonneg.mpr hx
  have hgi (n : ℕ) : Integrable (fun x => F n x - h x) μ := (hF n).sub hh
  have hdiffbound (n : ℕ) :
      (∫ x, F n x - h x ∂μ) ≤ B - ∫ x, h x ∂μ := by
    rw [integral_sub (hF n) hh]
    exact sub_le_sub_right (hbound n) _
  have hcap : 0 ≤ B - ∫ x, h x ∂μ :=
    (integral_nonneg_of_ae (hnonneg 0)).trans (hdiffbound 0)
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => ENNReal.ofReal (F n x - h x)) atTop
        (𝓝 (ENNReal.ofReal (f x - h x))) := by
    filter_upwards [hlim] with x hx
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp (hx.sub_const (h x))
  have hfatou : (∫⁻ x, ENNReal.ofReal (f x - h x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x - h x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (F n x - h x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpoint] with x hx using hx.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun n =>
        (hgi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hcomparison : ∀ᶠ n in atTop,
      (∫⁻ x, ENNReal.ofReal (F n x - h x) ∂μ) ≤
        ENNReal.ofReal (B - ∫ x, h x ∂μ) := by
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal (hdiffbound n)
  have htotal : (∫⁻ x, ENNReal.ofReal (f x - h x) ∂μ) ≤
      ENNReal.ofReal (B - ∫ x, h x ∂μ) := by
    exact hfatou.trans ((liminf_le_liminf hcomparison).trans_eq
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => ENNReal.ofReal (B - ∫ x, h x ∂μ)) atTop
        (𝓝 (ENNReal.ofReal (B - ∫ x, h x ∂μ)))).liminf_eq)
  have hdiffi : Integrable (fun x => f x - h x) μ := by
    refine ⟨hfm.sub hh.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hfn]
    exact htotal.trans_lt ENNReal.ofReal_lt_top
  have hfi : Integrable f μ := by
    apply (hdiffi.add hh).congr
    exact ae_of_all _ (fun x => sub_add_cancel (f x) (h x))
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hdiffi hfn] at htotal
  have hreal := (ENNReal.ofReal_le_ofReal_iff hcap).mp htotal
  rw [integral_sub hfi hh] at hreal
  exact (sub_le_sub_iff_right (∫ x, h x ∂μ)).mp hreal

open PhysicalFiniteFourier

/--
A direct specialization to actual finite Fourier kernels. The convergence
and integrable lower bound are explicit hypotheses on the product space;
the finite approximants' integrability and spectral identity are proved
in `PhysicalFiniteFourier`, not additional assumptions.
-/
theorem physical_kernel_integrable_and_energy_le
    {d : ℕ} (rho : ProbabilityDensity d)
    (s : ℕ → Finset (Frequency d)) (b : ℕ → Frequency d → ℝ)
    (K : Torus d → ℝ) (L : Torus d × Torus d → ℝ) (B : ℝ)
    (hL : Integrable L ((torusMeasure d).prod (torusMeasure d)))
    (hlower : ∀ n, ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
      L xy ≤ finiteKernel (s n) (b n) (xy.1 - xy.2) *
        rho.value xy.1 * rho.value xy.2)
    (hlim : ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
      Tendsto (fun n => finiteKernel (s n) (b n) (xy.1 - xy.2)) atTop
        (𝓝 (K (xy.1 - xy.2))))
    (hbound : ∀ n,
      (∑ k ∈ s n, b n k * ‖densityFourier rho.value k‖ ^ 2) ≤ B) :
    Integrable (fun xy : Torus d × Torus d =>
      K (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)
      ((torusMeasure d).prod (torusMeasure d)) ∧
    (∫ x, ∫ y, K (x - y) * rho.value x * rho.value y
      ∂torusMeasure d ∂torusMeasure d) ≤ B := by
  have hseq (n : ℕ) := finiteKernel_interaction_integrable rho (s n) (b n)
  have hlim' : ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
      Tendsto (fun n => finiteKernel (s n) (b n) (xy.1 - xy.2) *
        rho.value xy.1 * rho.value xy.2) atTop
        (𝓝 (K (xy.1 - xy.2) * rho.value xy.1 * rho.value xy.2)) := by
    filter_upwards [hlim] with xy hxy
    exact (hxy.mul_const (rho.value xy.1)).mul_const (rho.value xy.2)
  have hspec (n : ℕ) :
      (∫ xy : Torus d × Torus d,
        finiteKernel (s n) (b n) (xy.1 - xy.2) *
          rho.value xy.1 * rho.value xy.2
          ∂(torusMeasure d).prod (torusMeasure d)) ≤ B := by
    rw [finiteKernel_product_integral]
    exact hbound n
  obtain ⟨hi, hb⟩ := integrable_and_integral_le_of_lower_bound
    ((torusMeasure d).prod (torusMeasure d)) _ _ L B hseq hL hlower hlim' hspec
  refine ⟨hi, ?_⟩
  rw [← integral_prod _ hi]
  exact hb

end Legacy.TorusEndpoint.LowerBoundedFatou

#print axioms Legacy.TorusEndpoint.LowerBoundedFatou.integrable_and_integral_le_of_lower_bound
#print axioms Legacy.TorusEndpoint.LowerBoundedFatou.physical_kernel_integrable_and_energy_le
