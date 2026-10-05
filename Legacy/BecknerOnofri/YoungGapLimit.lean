import Legacy.BecknerOnofri.EntropyVariationalEquality
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Fatou transfers vanishing integrals of actual nonnegative Young gaps to
an almost-everywhere Gibbs identity, without any L2 assumption on the density. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace Legacy.BecknerOnofri.YoungGapLimit
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem nonnegative_limit_zero_of_integrals {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hfn : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hI : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0)) : g =ᵐ[μ] fun _ => 0 := by
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (f n x)) atTop (𝓝 (ENNReal.ofReal (g x))) :=
    hlim.mono (fun x hx => (ENNReal.continuous_ofReal.tendsto _).comp hx)
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (g x)) μ :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hfi n).aemeasurable.ennreal_ofReal) hlim'
  have hI' : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop (𝓝 0) := by
    have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f n x) ∂μ) = ENNReal.ofReal (∫ x, f n x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal (hfi n) (hfn n)).symm
    simp_rw [he]
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hI
  have hfat : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ (0:ℝ≥0∞) := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        exact hlim'.mono (fun _ hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hfi n).aemeasurable.ennreal_ofReal)
      _ = 0 := hI'.liminf_eq
  have hgzero := (lintegral_eq_zero_iff' hgm).mp (le_antisymm hfat bot_le)
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f n x := ae_all_iff.mpr hfn
  filter_upwards [hgzero,hlim,hall] with x hz hx hn
  have hg : 0 ≤ g x := ge_of_tendsto hx (Filter.Eventually.of_forall hn)
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) hg

def gap (rho v : X → ℝ) (ell : ℝ) (x : X) : ℝ :=
  rho x*Real.log (rho x)-rho x-rho x*(v x-ell)+Real.exp (v x-ell)

omit [MeasurableSpace X] in
theorem gap_nonnegative {rho v : X → ℝ} {ell : ℝ} {x : X} (hr : 0 ≤ rho x) :
    0 ≤ gap rho v ell x := by
  have h := Legacy.TorusEndpoint.entropy_young (rho x) (v x-ell) hr
  unfold gap
  linarith

omit [MeasurableSpace X] in
theorem gap_eq_zero_iff {rho v : X → ℝ} {ell : ℝ} {x : X} (hr : 0 ≤ rho x) :
    gap rho v ell x = 0 ↔ rho x = Real.exp (v x-ell) := by
  rw [← EntropyVariationalEquality.entropy_young_eq_iff hr]
  unfold gap
  constructor <;> intro h <;> linarith

theorem eq_exp_of_gap_integrals_tendsto_zero {rho v : X → ℝ} {vn : ℕ → X → ℝ}
    {elln : ℕ → ℝ} {ell : ℝ}
    (hr : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (hgap : ∀ n, Integrable (gap rho (vn n) (elln n)) μ)
    (hv : ∀ᵐ x ∂μ, Tendsto (fun n => vn n x) atTop (𝓝 (v x)))
    (hell : Tendsto elln atTop (𝓝 ell))
    (hI : Tendsto (fun n => ∫ x, gap rho (vn n) (elln n) x ∂μ) atTop (𝓝 0)) :
    rho =ᵐ[μ] fun x => Real.exp (v x-ell) := by
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => gap rho (vn n) (elln n) x) atTop (𝓝 (gap rho v ell x)) := by
    filter_upwards [hv] with x hx
    exact ((tendsto_const_nhds.sub (tendsto_const_nhds.mul (hx.sub hell))).add
      ((Real.continuous_exp.tendsto _).comp (hx.sub hell)))
  have hz := nonnegative_limit_zero_of_integrals hgap (fun n => hr.mono (fun _ hx => gap_nonnegative hx)) hlim hI
  filter_upwards [hr,hz] with x hx hz
  exact (gap_eq_zero_iff hx).mp hz

theorem eq_normalized_exp_of_gap_integrals_tendsto_zero {rho v : X → ℝ} {vn : ℕ → X → ℝ}
    {Zn : ℕ → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hr : ∀ᵐ x ∂μ, 0 ≤ rho x)
    (hgap : ∀ n, Integrable (gap rho (vn n) (Real.log (Zn n))) μ)
    (hv : ∀ᵐ x ∂μ, Tendsto (fun n => vn n x) atTop (𝓝 (v x)))
    (hZlim : Tendsto Zn atTop (𝓝 Z))
    (hI : Tendsto (fun n => ∫ x, gap rho (vn n) (Real.log (Zn n)) x ∂μ) atTop (𝓝 0)) :
    rho =ᵐ[μ] fun x => Real.exp (v x)/Z := by
  have h := eq_exp_of_gap_integrals_tendsto_zero hr hgap hv
    ((Real.continuousAt_log hZ.ne').tendsto.comp hZlim) hI
  simpa only [Real.exp_sub,Real.exp_log hZ] using h

#print axioms nonnegative_limit_zero_of_integrals
#print axioms eq_exp_of_gap_integrals_tendsto_zero
end Legacy.BecknerOnofri.YoungGapLimit
