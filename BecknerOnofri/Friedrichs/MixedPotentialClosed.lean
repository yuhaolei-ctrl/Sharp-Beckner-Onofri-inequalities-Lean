import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-! Closedness of multiplication by the actual singular potential factor.
The proof uses almost-everywhere subsequences of L2 limits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma multiplication_relation_isClosed {d : ℕ} (α : MultiIndex d) (W : Space d → ℝ) :
    IsClosed {v : H α × H α | (v.2 : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => W x*v.1 x)} := by
  apply IsSeqClosed.isClosed
  intro u v hu huv
  have hf0 : Tendsto (fun n => (u n).1) atTop (𝓝 v.1) := (continuous_fst.tendsto v).comp huv
  have hg0 : Tendsto (fun n => (u n).2) atTop (𝓝 v.2) := (continuous_snd.tendsto v).comp huv
  obtain ⟨ns,hns,hf⟩ := (tendstoInMeasure_of_tendsto_Lp hf0).exists_seq_tendsto_ae
  obtain ⟨ms,hms,hg⟩ := (tendstoInMeasure_of_tendsto_Lp (hg0.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂spatialMeasure α,∀ n,(u n).2 x=W x*(u n).1 x := ae_all_iff.mpr hu
  filter_upwards [hf,hg,he] with x hfx hgx hex
  have hh := (tendsto_const_nhds (x := W x)).mul (hfx.comp hms.tendsto_atTop)
  exact tendsto_nhds_unique hgx (hh.congr (fun n => (hex (ns (ms n))).symm))

lemma closed_potential_relation {d : ℕ} {α : MultiIndex d} {v : EnergySpace α}
    (hv : v∈formClosure α) (i : Fin d) :
    (v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => SpatialForm.potentialFactor (α i) (x i)*v.1 x) := by
  have hp : Continuous (fun v : EnergySpace α => (v.1,v.2.2 i)) := by fun_prop
  have hc : IsClosed {v : EnergySpace α | (v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => SpatialForm.potentialFactor (α i) (x i)*v.1 x)} :=
    (multiplication_relation_isClosed α (fun x => SpatialForm.potentialFactor (α i) (x i))).preimage
      hp
  apply closure_minimal (t := {v : EnergySpace α | (v.2.2 i : Space d → ℝ)=ᵐ[spatialMeasure α]
      (fun x => SpatialForm.potentialFactor (α i) (x i)*v.1 x)}) ?_ hc hv
  rintro u ⟨F,hF,hu0,hu1,huV⟩
  filter_upwards [hu0,huV i] with x hx hy
  rw [hy,hx]

#print axioms closed_potential_relation
end BecknerOnofri.Friedrichs.MixedSpatial
