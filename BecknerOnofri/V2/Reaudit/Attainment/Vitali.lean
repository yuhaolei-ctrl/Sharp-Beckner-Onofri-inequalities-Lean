module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! # Vitali's theorem in the form used for `∫ e^{u_n} → ∫ e^u` (package `Attainment`)

A sequence of functions that is bounded in `L²` of a finite measure is uniformly integrable in
`L¹`; together with almost-everywhere convergence to an integrable function, Vitali's theorem
(`MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`) gives convergence of the integrals.  This is the
step "`(e^{u_n})` is bounded in `L²`, hence uniformly integrable; Vitali gives
`eq:section2-exponential-vitali`" of the printed proof of `prop:section2-subcritical-attainment`. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace BecknerOnofri.V2.Reaudit.Attainment

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem unifIntegrable_of_sq_bound_aux {F : ℕ → α → ℝ} (hF : ∀ n, StronglyMeasurable (F n))
    (hint : ∀ n, Integrable (fun x => F n x ^ 2) μ) {M : ℝ}
    (hM : ∀ n, ∫ x, F n x ^ 2 ∂μ ≤ M) : UnifIntegrable F 1 μ := by
  refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hF n).aestronglyMeasurable)
    fun ε hε => ?_
  by_cases hεtop : ε = ∞
  · exact ⟨1, fun n => by rw [hεtop]; exact le_top⟩
  set e : ℝ := ε.toReal with he
  have hepos : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal hεtop).symm
  have hC1 : (0 : ℝ) ≤ max (M / e) 1 := le_trans zero_le_one (le_max_right _ _)
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ≥0, (C' : ℝ) = max (M / e) 1 := ⟨⟨_, hC1⟩, rfl⟩
  refine ⟨C', fun n => ?_⟩
  set C : ℝ := max (M / e) 1 with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hset : MeasurableSet {x | C' ≤ ‖F n x‖₊} :=
    measurableSet_le measurable_const (hF n).nnnorm.measurable
  have hpt : ∀ x, ‖({x | C' ≤ ‖F n x‖₊}.indicator (F n)) x‖ₑ ≤
      ‖F n x ^ 2 / C‖ₑ := by
    intro x
    by_cases hx : C' ≤ ‖F n x‖₊
    · rw [Set.indicator_of_mem (by exact hx), Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      have hxC : C ≤ |F n x| := by
        have : ((C' : ℝ≥0) : ℝ) ≤ ‖F n x‖₊ := hx
        rw [hC'] at this
        simpa [Real.norm_eq_abs] using this
      rw [abs_div, abs_of_pos hCpos, abs_pow, le_div_iff₀ hCpos]
      nlinarith [abs_nonneg (F n x)]
    · rw [Set.indicator_of_notMem (by exact hx)]
      simp
  have hgm : AEStronglyMeasurable (fun x => F n x ^ 2 / C) μ := ((hint n).div_const C).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[μ] fun x => F n x ^ 2 / C := Eventually.of_forall fun x => by positivity
  calc eLpNorm ({x | C' ≤ ‖F n x‖₊}.indicator (F n)) 1 μ
      ≤ eLpNorm (fun x => F n x ^ 2 / C) 1 μ :=
        eLpNorm_mono_enorm ((hF n).aestronglyMeasurable.indicator hset) hpt
    _ = ∫⁻ x, ENNReal.ofReal (F n x ^ 2 / C) ∂μ := by
        rw [eLpNorm_one_eq_lintegral_enorm hgm]
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_eq_ofReal (by positivity)]
    _ = ENNReal.ofReal (∫ x, F n x ^ 2 / C ∂μ) := by
        rw [ofReal_integral_eq_lintegral_ofReal ((hint n).div_const C) hnn]
    _ ≤ ε := by
        rw [hεe]
        apply ENNReal.ofReal_le_ofReal
        rw [integral_div, div_le_iff₀ hCpos]
        have h1 : M / e ≤ C := le_max_left _ _
        have h2 : M ≤ e * C := by rwa [div_le_iff₀ hepos, mul_comm] at h1
        linarith [hM n]

/-- A family bounded in `L²` is uniformly integrable in `L¹`. -/
theorem unifIntegrable_of_sq_bound {F : ℕ → α → ℝ} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : ∀ n, Integrable (fun x => F n x ^ 2) μ) {M : ℝ}
    (hM : ∀ n, ∫ x, F n x ^ 2 ∂μ ≤ M) : UnifIntegrable F 1 μ := by
  set G : ℕ → α → ℝ := fun n => (hF n).mk (F n) with hG
  have hae : ∀ n, F n =ᵐ[μ] G n := fun n => (hF n).ae_eq_mk
  have hGm : ∀ n, StronglyMeasurable (G n) := fun n => (hF n).stronglyMeasurable_mk
  have hae2 : ∀ n, (fun x => F n x ^ 2) =ᵐ[μ] fun x => G n x ^ 2 := fun n => by
    filter_upwards [hae n] with x hx
    rw [hx]
  have hGi : ∀ n, Integrable (fun x => G n x ^ 2) μ := fun n => (hint n).congr (hae2 n)
  have hGM : ∀ n, ∫ x, G n x ^ 2 ∂μ ≤ M := fun n => by
    rw [← integral_congr_ae (hae2 n)]
    exact hM n
  exact (unifIntegrable_of_sq_bound_aux hGm hGi hGM).ae_eq (fun n => (hae n).symm)


/-- Vitali's theorem in the form used for `∫ e^{u_n} → ∫ e^u`: almost-everywhere convergence and a
uniform `L²` bound give convergence of the integrals, once the limit is integrable. -/
theorem tendsto_integral_of_ae_of_sq_bound [IsFiniteMeasure μ] {F : ℕ → α → ℝ} {G : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hint : ∀ n, Integrable (fun x => F n x ^ 2) μ)
    {M : ℝ} (hM : ∀ n, ∫ x, F n x ^ 2 ∂μ ≤ M) (hG : Integrable G μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, G x ∂μ)) := by
  have hUI := unifIntegrable_of_sq_bound hF hint hM
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hF
    (memLp_one_iff_integrable.mpr hG) hUI hae
  have hFi : ∀ n, Integrable (F n) μ := fun n =>
    ((memLp_two_iff_integrable_sq (hF n)).mpr (hint n)).integrable (by norm_num)
  refine tendsto_integral_of_L1 G hG.aestronglyMeasurable (Eventually.of_forall hFi) ?_
  refine hL1.congr fun n => ?_
  exact eLpNorm_one_eq_lintegral_enorm ((hF n).sub hG.aestronglyMeasurable)

end BecknerOnofri.V2.Reaudit.Attainment
