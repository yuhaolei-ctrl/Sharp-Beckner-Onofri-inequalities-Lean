module

public import Legacy.TorusEndpoint.GreenHeatRegularization
public import Legacy.TorusEndpoint.GreenKernelApproximation

@[expose] public section

/-!
# Actual almost-everywhere heat approximation of the Green kernel

The real parts of the continuous, Gaussian-damped Fourier kernels converge
in L2. An actual subsequence converges almost everywhere, also after the
product-space subtraction map. No pointwise lower bound is asserted here.
-/

open MeasureTheory Filter
open scoped Topology

namespace Legacy.TorusEndpoint.GreenHeatApproximation

open GreenHeatRegularization GreenKernelReal GreenMultiplierSummability GreenKernelApproximation

noncomputable def realHeatGreenLp {d : ℕ} {t : ℝ} (ht : 0 < t) : Lp ℝ 2 (torusMeasure d) :=
  Complex.reCLM.compLp (heatGreenLp (d := d) ht)

theorem realHeatGreenLp_coe_ae {d : ℕ} {t : ℝ} (ht : 0 < t) :
    realHeatGreenLp (d := d) ht =ᵐ[torusMeasure d] (fun x => (heatGreenKernel d t x).re) := by
  filter_upwards [Complex.reCLM.coeFn_compLp (heatGreenLp (d := d) ht),
    heatGreenLp_coe_ae (d := d) ht] with x hx hy
  change realHeatGreenLp ht x = (heatGreenLp ht x).re at hx
  rw [hx, hy]

theorem realHeatGreenLp_tendsto {d : ℕ} (t : ℕ → ℝ) (hpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => realHeatGreenLp (d := d) (hpos n)) atTop (𝓝 (realGreenLp d)) := by
  have hc : Continuous
      (Complex.reCLM.compLp : Lp ℂ 2 (torusMeasure d) → Lp ℝ 2 (torusMeasure d)) :=
    Complex.reCLM.lipschitz.continuous_compLp (map_zero Complex.reCLM)
  exact (hc.tendsto (greenL2 d)).comp (heatGreenLp_tendsto t hpos ht)

theorem exists_subsequence_heatGreen_tendsto_ae {d : ℕ}
    (t : ℕ → ℝ) (hpos : ∀ n, 0 < t n) (ht : Tendsto t atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂torusMeasure d,
      Tendsto (fun n => (heatGreenKernel d (t (ns n)) x).re) atTop (𝓝 (realGreen d x)) := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (realHeatGreenLp_tendsto (d := d) t hpos ht)).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, ae_all_iff.mpr (fun n => realHeatGreenLp_coe_ae (d := d) (hpos n)),
    realGreenLp_coe_ae d] with x hx hy hz
  simpa only [hy, hz] using hx

noncomputable def heatTime (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem heatTime_pos (n : ℕ) : 0 < heatTime n := by
  unfold heatTime
  positivity

theorem heatTime_tendsto : Tendsto heatTime atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_heatGreen_tendsto_sub_ae (d : ℕ) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n) ∧ Tendsto t atTop (𝓝 0) ∧
      ∀ᵐ xy ∂(torusMeasure d).prod (torusMeasure d),
        Tendsto (fun n => (heatGreenKernel d (t n) (xy.1 - xy.2)).re) atTop
          (𝓝 (realGreen d (xy.1 - xy.2))) := by
  obtain ⟨ns, hns, hae⟩ :=
    exists_subsequence_heatGreen_tendsto_ae (d := d) heatTime heatTime_pos heatTime_tendsto
  exact ⟨heatTime ∘ ns, fun n => heatTime_pos (ns n),
    heatTime_tendsto.comp hns.tendsto_atTop, ae_subtraction hae⟩

end Legacy.TorusEndpoint.GreenHeatApproximation
