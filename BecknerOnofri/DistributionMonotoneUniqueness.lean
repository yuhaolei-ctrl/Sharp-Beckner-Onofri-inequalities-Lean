import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Equimeasurability uniquely determines a decreasing function of a common
real-valued radius, up to null sets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BecknerOnofri.DistributionLimit

theorem ae_eq_of_identDistrib_antitone_radius {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (r : α → ℝ) {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hD : IdentDistrib f g μ μ)
    (hfR : ∀ x y,r x≤r y → f y≤f x) (hgR : ∀ x y,r x≤r y → g y≤g x) :
    f=ᵐ[μ] g := by
  have hlevels (t : ℝ) : {x | t<f x}=ᵐ[μ] {x | t<g x} := by
    have hm := hD.measure_mem_eq (s := Ioi t) measurableSet_Ioi
    have hfm : MeasurableSet {x | t<f x} := measurableSet_lt measurable_const hf
    have hgm : MeasurableSet {x | t<g x} := measurableSet_lt measurable_const hg
    by_cases hsub : {x | t<f x}⊆{x | t<g x}
    · exact ae_eq_of_subset_of_measure_ge hsub hm.ge hfm.nullMeasurableSet (measure_ne_top _ _)
    · have hrev : {x | t<g x}⊆{x | t<f x} := by
        obtain ⟨x,hxf,hxg⟩ := Set.not_subset.mp hsub
        intro y hyt
        have hxy : r y≤r x := by
          by_contra h
          have hgxy := hgR x y (le_of_not_ge h)
          exact hxg (lt_of_lt_of_le hyt hgxy)
        exact lt_of_lt_of_le hxf (hfR y x hxy)
      exact (ae_eq_of_subset_of_measure_ge hrev hm.le hgm.nullMeasurableSet (measure_ne_top _ _)).symm
  have hall : ∀ᵐ x ∂μ,∀ t : ℚ,((t : ℝ)<f x ↔ (t : ℝ)<g x) :=
    ae_all_iff.mpr (fun t => (hlevels t).mono (fun _ hx => Iff.of_eq hx))
  filter_upwards [hall] with x hx
  apply le_antisymm
  · by_contra h
    obtain ⟨t,hgt,htf⟩ := exists_rat_btwn (lt_of_not_ge h)
    exact (not_lt_of_ge hgt.le) ((hx t).mp htf)
  · by_contra h
    obtain ⟨t,hft,htg⟩ := exists_rat_btwn (lt_of_not_ge h)
    exact (not_lt_of_ge hft.le) ((hx t).mpr htg)

#print axioms ae_eq_of_identDistrib_antitone_radius
end BecknerOnofri.DistributionLimit
