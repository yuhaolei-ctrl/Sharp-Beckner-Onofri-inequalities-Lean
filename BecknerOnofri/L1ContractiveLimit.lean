import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Completeness in the concrete integral L1 metric and transfer of Cauchy
convergence under a contractive transformation of an approximating sequence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.RearrangementApproximation

lemma dist_toL1_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g)=∫ x,‖f x-g x‖ ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1,hg.coeFn_toL1] with x hx hy
  rw [hx,hy,dist_eq_norm]

lemma tendsto_toL1_iff {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ n,Integrable (f n) μ) (hg : Integrable g μ) :
    Tendsto (fun n => (hf n).toL1 (f n)) l (𝓝 (hg.toL1 g)) ↔
      Tendsto (fun n => ∫ x,‖f n x-g x‖ ∂μ) l (𝓝 0) := by
  constructor
  · intro h
    have ht := h.dist (tendsto_const_nhds (x := hg.toL1 g))
    simpa only [dist_self,dist_toL1_eq] using ht
  · intro h
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_toL1_eq] using h

theorem exists_l1_limit_of_contractive_sequence {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : ℕ → α → ℝ} {f₀ : α → ℝ}
    (hf : ∀ n,Integrable (f n) μ) (hg : ∀ n,Integrable (g n) μ)
    (hf₀ : Integrable f₀ μ)
    (hlim : Tendsto (fun n => ∫ x,‖f n x-f₀ x‖ ∂μ) atTop (𝓝 0))
    (hcontract : ∀ n m,(∫ x,‖g n x-g m x‖ ∂μ)≤∫ x,‖f n x-f m x‖ ∂μ) :
    ∃ g₀ : α → ℝ,Integrable g₀ μ ∧
      Tendsto (fun n => ∫ x,‖g n x-g₀ x‖ ∂μ) atTop (𝓝 0) := by
  have hF := (tendsto_toL1_iff hf hf₀).mpr hlim
  have hFc := Metric.cauchySeq_iff.mp hF.cauchySeq
  have hGc : CauchySeq (fun n => (hg n).toL1 (g n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hFc ε hε
    refine ⟨N,fun n hn m hm => ?_⟩
    rw [dist_toL1_eq]
    exact (hcontract n m).trans_lt (by simpa only [dist_toL1_eq] using hN n hn m hm)
  obtain ⟨G,hG⟩ := cauchySeq_tendsto_of_complete hGc
  have hGi : Integrable G μ := L1.integrable_coeFn G
  refine ⟨G,hGi,?_⟩
  apply (tendsto_toL1_iff hg hGi).mp
  simpa only [Integrable.toL1_coeFn] using hG

#print axioms exists_l1_limit_of_contractive_sequence
end BecknerOnofri.RearrangementApproximation
