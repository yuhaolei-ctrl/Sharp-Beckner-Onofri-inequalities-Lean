module

public import BecknerOnofri.DistributionMonotoneUniqueness

@[expose] public section

/-! A representative-independent characterization of symmetric decreasing
L1 functions: antitonicity in radius on a set of full measure. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace BecknerOnofri.DistributionLimit

def AntitoneRadiusAE {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (r : α → ℝ) (f : α → ℝ) : Prop :=
  ∃ s : Set α,(∀ᵐ x ∂μ,x∈s) ∧ ∀ x∈s,∀ y∈s,r x≤r y → f y≤f x

theorem ae_eq_of_identDistrib_antitoneRadiusAE {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {r : α → ℝ} {f g : α → ℝ}
    (hD : IdentDistrib f g μ μ) (hfR : AntitoneRadiusAE μ r f)
    (hgR : AntitoneRadiusAE μ r g) : f=ᵐ[μ] g := by
  obtain ⟨s,hs,hfS⟩ := hfR
  obtain ⟨u,hu,hgS⟩ := hgR
  have hsu : ∀ᵐ x ∂μ,x∈s∩u := hs.and hu
  have hlevels (t : ℝ) : {x | t<f x}=ᵐ[μ] {x | t<g x} := by
    have hm := hD.measure_mem_eq (s := Ioi t) measurableSet_Ioi
    have hfm : NullMeasurableSet {x | t<f x} μ :=
      hD.aemeasurable_fst.nullMeasurable measurableSet_Ioi
    have hgm : NullMeasurableSet {x | t<g x} μ :=
      hD.aemeasurable_snd.nullMeasurable measurableSet_Ioi
    by_cases hsub : ∀ x∈s∩u,t<f x → t<g x
    · have ha : {x | t<f x}≤ᵐ[μ] {x | t<g x} := by
        filter_upwards [hsu] with x hx
        exact hsub x hx
      exact ae_eq_of_ae_subset_of_measure_ge ha hm.ge hfm (measure_ne_top _ _)
    · push_neg at hsub
      obtain ⟨x,hxs,hxf,hxg⟩ := hsub
      have ha : {x | t<g x}≤ᵐ[μ] {x | t<f x} := by
        filter_upwards [hsu] with y hys
        intro hyt
        have hxy : r y≤r x := by
          by_contra h
          have hgxy := hgS x hxs.2 y hys.2 (le_of_not_ge h)
          exact (not_lt_of_ge hxg) (lt_of_lt_of_le hyt hgxy)
        exact lt_of_lt_of_le hxf (hfS y hys.1 x hxs.1 hxy)
      exact (ae_eq_of_ae_subset_of_measure_ge ha hm.le hgm (measure_ne_top _ _)).symm
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

#print axioms ae_eq_of_identDistrib_antitoneRadiusAE
end BecknerOnofri.DistributionLimit
