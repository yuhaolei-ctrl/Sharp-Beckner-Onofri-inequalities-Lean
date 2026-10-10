module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

/-! # Vitali's theorem for sequences bounded in `L²` (uniform exponential moments)

Manuscript (Section 4, proof of `prop:section4-first-order-coexistence`):
"`(e^{u_n})` is uniformly integrable, and almost-everywhere convergence and Vitali's theorem imply
`∫ e^{u_n} → ∫ e^{u_0}`" (`eq:section4-vitali-exponential`), and, under `u_0 = 0`,
"`\sup_n ∫ e^{4u_n} < ∞` makes `(e^{u_n} - 1)²` uniformly integrable; Vitali's theorem gives
`ρ_n → 1` in `L²`" (`eq:section4-rho-n-to-one-L2`).

Both applications use the same elementary fact: on a probability space a sequence bounded in
`L²` is uniformly integrable (Hölder on the restriction to a small set), hence by Vitali's theorem
(Mathlib's `tendsto_Lp_finite_of_tendsto_ae`) an a.e. convergent such sequence converges in `L¹`. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BecknerOnofri.V2.Reaudit.Compactness

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A sequence bounded in `L²` of a finite measure is uniformly integrable (in the `L¹` sense). -/
theorem unifIntegrable_one_of_L2_bound [IsFiniteMeasure μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (K : ℝ≥0) (hK : ∀ n, eLpNorm (f n) 2 μ ≤ K) :
    UnifIntegrable f 1 μ := by
  rw [unifIntegrable_iff']
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨1, one_pos, fun i s _ _ => by simp [hεtop]⟩
  lift ε to ℝ≥0 using hεtop
  have hε' : 0 < ε := by exact_mod_cast hε
  set δ' : ℝ≥0 := (ε / (K + 1)) ^ 2 with hδ'
  have hδpos : 0 < δ' := by positivity
  refine ⟨(δ' : ℝ≥0∞), by exact_mod_cast hδpos, fun i s hs hμs => ?_⟩
  have h1 : eLpNorm (f i) 1 (μ.restrict s) ≤
      eLpNorm (f i) 2 (μ.restrict s) * (μ.restrict s) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) ((hf i).mono_measure Measure.restrict_le_self)
  have h2 : eLpNorm (f i) 2 (μ.restrict s) ≤ K :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hK i)
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]; norm_num
  rw [hexp, Measure.restrict_apply_univ] at h1
  have h3 : μ s ^ (1 / 2 : ℝ) ≤ ((δ' : ℝ≥0∞)) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hμs (by norm_num)
  have h4 : ((δ' : ℝ≥0∞)) ^ (1 / 2 : ℝ) = ((ε / (K + 1) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_rpow_of_nonneg _ (by norm_num), hδ']
    congr 1
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    norm_num
  calc eLpNorm (f i) 1 (μ.restrict s)
      ≤ eLpNorm (f i) 2 (μ.restrict s) * μ s ^ (1 / 2 : ℝ) := h1
    _ ≤ (K : ℝ≥0∞) * ((ε / (K + 1) : ℝ≥0) : ℝ≥0∞) := by
        rw [← h4]; exact mul_le_mul' h2 h3
    _ = ((K * (ε / (K + 1)) : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
    _ ≤ (ε : ℝ≥0∞) := by
        rw [ENNReal.coe_le_coe]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        rw [mul_comm]
        gcongr
        exact le_self_add

/-- **Vitali's theorem, `L²`-bounded form.**  A sequence of real functions on a probability space
with `∫ f_n² ≤ M` converging a.e. to an integrable `g` converges to `g` in `L¹`. -/
theorem tendsto_lintegral_enorm_sub_of_sq_bound [IsProbabilityMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hfi : ∀ n, Integrable (fun x => f n x ^ 2) μ)
    (M : ℝ) (hM : ∀ n, ∫ x, f n x ^ 2 ∂μ ≤ M)
    (hg : Integrable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ∂μ) atTop (𝓝 0) := by
  have hmem : ∀ n, MemLp (f n) 2 μ := fun n => (memLp_two_iff_integrable_sq (hfm n)).2 (hfi n)
  have hK : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (Real.sqrt (max M 0)) := by
    intro n
    have h := (hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [h]
    apply ENNReal.ofReal_le_ofReal
    have e : ∫ x, ‖f n x‖ ^ (2 : ENNReal).toReal ∂μ = ∫ x, f n x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [sq_abs]
    rw [e]
    simp only [ENNReal.toReal_ofNat]
    have hnn : 0 ≤ ∫ x, f n x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    calc (∫ x, f n x ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹) = Real.sqrt (∫ x, f n x ^ 2 ∂μ) := by
          rw [Real.sqrt_eq_rpow, one_div]
      _ ≤ _ := Real.sqrt_le_sqrt ((hM n).trans (le_max_left _ _))
  set K : ℝ≥0 := (Real.sqrt (max M 0)).toNNReal with hKdef
  have hK' : ∀ n, eLpNorm (f n) 2 μ ≤ K := by
    intro n; simpa [hKdef, ENNReal.ofReal] using hK n
  have hui := unifIntegrable_one_of_L2_bound hfm K hK'
  have hv := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl ENNReal.one_ne_top hfm
    (memLp_one_iff_integrable.2 hg) hui hae
  refine hv.congr fun n => ?_
  rw [eLpNorm_one_eq_lintegral_enorm ((hfm n).sub hg.aestronglyMeasurable)]
  rfl

/-- The integrals converge. -/
theorem tendsto_integral_of_sq_bound [IsProbabilityMeasure μ] {f : ℕ → α → ℝ} {g : α → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hfi : ∀ n, Integrable (fun x => f n x ^ 2) μ)
    (M : ℝ) (hM : ∀ n, ∫ x, f n x ^ 2 ∂μ ≤ M)
    (hg : Integrable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hmem : ∀ n, Integrable (f n) μ := fun n =>
    ((memLp_two_iff_integrable_sq (hfm n)).2 (hfi n)).integrable (by norm_num)
  exact tendsto_integral_of_L1 g hg.aestronglyMeasurable (Eventually.of_forall hmem)
    (tendsto_lintegral_enorm_sub_of_sq_bound hfm hfi M hM hg hae)

end BecknerOnofri.V2.Reaudit.Compactness
