module

public import BecknerOnofri.Friedrichs.MixedCutoffL2

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma coordinate_ae_compact (m : ℕ) :
    ∀ᵐ t ∂coordinateMeasure m,t∈Icc 0 (2*Real.pi) := by
  unfold coordinateMeasure
  split_ifs
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ⟨ht.1.le,ht.2⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ⟨ht.1.le,ht.2.le.trans (by linarith [Real.pi_pos])⟩

lemma spatial_ae_compact {d : ℕ} (α : MultiIndex d) :
    ∀ᵐ x ∂spatialMeasure α,x∈Icc (0 : Space d) (fun _ => 2*Real.pi) := by
  have h : ∀ᵐ x ∂spatialMeasure α,∀ i,x i∈Icc 0 (2*Real.pi) := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun j : Fin d => coordinateMeasure (α j)) (i := i)).eventually
      (coordinate_ae_compact (α i))
  filter_upwards [h] with x hx
  exact ⟨fun i => (hx i).1,fun i => (hx i).2⟩

lemma continuous_memLp {d : ℕ} (α : MultiIndex d) {F : Space d → ℝ} (hF : Continuous F) :
    MemLp F 2 (spatialMeasure α) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : Space d) (fun _ => 2*Real.pi)) hF.continuousOn
  apply MemLp.of_bound hF.aestronglyMeasurable C
  filter_upwards [spatial_ae_compact α] with x hx
  exact hC x hx

lemma continuous_square_integrable {d : ℕ} (α : MultiIndex d) {F : Space d → ℝ} (hF : Continuous F) :
    Integrable (fun x => (F x)^2) (spatialMeasure α) :=
  (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mp (continuous_memLp α hF)

#print axioms continuous_memLp
end BecknerOnofri.Friedrichs.MixedSpatial
