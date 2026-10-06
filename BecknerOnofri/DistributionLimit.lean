module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Distributional constraints survive convergence in measure. This is the
closedness step for the L1 closure of a polarization orbit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BecknerOnofri.DistributionLimit

/-- A limit in measure of functions with a fixed real distribution has that
same distribution. The limit need not be supplied with a measurability premise. -/
theorem identDistrib_of_tendstoInMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : ℕ → α → ℝ} {g : β → ℝ} {h : α → ℝ}
    (hd : ∀ n, IdentDistrib (f n) g μ ν)
    (hc : TendstoInMeasure μ f atTop h) : IdentDistrib h g μ ν := by
  have hh := hc.aemeasurable (fun n => (hd n).aemeasurable_fst)
  refine ⟨hh,(hd 0).aemeasurable_snd,?_⟩
  obtain ⟨ns,_,hns⟩ := hc.exists_seq_tendsto_ae
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hh φ.continuous.aestronglyMeasurable,
    integral_map (hd 0).aemeasurable_snd φ.continuous.aestronglyMeasurable]
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n x => φ (f (ns n) x)) (f := fun x => φ (h x)) (fun _ : α => ‖φ‖)
    (fun n => (φ.continuous.measurable.comp_aemeasurable (hd (ns n)).aemeasurable_fst).aestronglyMeasurable)
    (integrable_const ‖φ‖)
    (fun n => Filter.Eventually.of_forall (fun x => φ.norm_coe_le_norm (f (ns n) x)))
    (hns.mono (fun x hx => φ.continuous.continuousAt.tendsto.comp hx))
  have he (n : ℕ) : (∫ x,φ (f (ns n) x) ∂μ) = ∫ x,φ (g x) ∂ν :=
    ((hd (ns n)).comp φ.continuous.measurable).integral_eq
  simp_rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

#print axioms identDistrib_of_tendstoInMeasure
end BecknerOnofri.DistributionLimit
