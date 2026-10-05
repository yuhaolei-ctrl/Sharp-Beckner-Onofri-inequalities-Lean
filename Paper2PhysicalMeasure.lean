import BecknerOnofri.Friedrichs.MixedSpatialDefinitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual unit-period mixed Lebesgue measure and the change from angles.
Inactive coordinates keep a full period; active coordinates are open half intervals. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial

def scale : ℝ := 2 * Real.pi
lemma scale_pos : 0 < scale := by unfold scale; positivity
lemma scale_ne : scale ≠ 0 := scale_pos.ne'

def coordinateMeasure (m : ℕ) : Measure ℝ :=
  if m=0 then volume.restrict (Ioc 0 1) else volume.restrict (Ioo 0 (1/2:ℝ))
instance (m : ℕ) : IsFiniteMeasure (coordinateMeasure m) := by
  unfold coordinateMeasure
  split_ifs <;> infer_instance

def spatialMeasure {d : ℕ} (α : MultiIndex d) : Measure (Space d) :=
  Measure.pi (fun i => coordinateMeasure (α i))
instance {d : ℕ} (α : MultiIndex d) : IsFiniteMeasure (spatialMeasure α) := by
  unfold spatialMeasure
  infer_instance
abbrev H {d : ℕ} (α : MultiIndex d) := Lp ℝ 2 (spatialMeasure α)

def down {d : ℕ} (x : Space d) : Space d := fun i => scale⁻¹ * x i
def up {d : ℕ} (x : Space d) : Space d := fun i => scale * x i
@[simp] lemma down_up {d : ℕ} (x : Space d) : down (up x) = x := by
  ext i
  simp [down,up,← mul_assoc,scale_ne]
@[simp] lemma up_down {d : ℕ} (x : Space d) : up (down x) = x := by
  ext i
  simp [down,up,← mul_assoc,scale_ne]

lemma map_coordinate (m : ℕ) :
    (Friedrichs.MixedSpatial.coordinateMeasure m).map (fun x => scale⁻¹*x) =
      ENNReal.ofReal scale • coordinateMeasure m := by
  have hm := Real.map_volume_mul_left (inv_ne_zero scale_ne)
  have hv : Measure.map (fun x : ℝ => scale⁻¹*x) volume = ENNReal.ofReal scale • volume := by
    simpa [abs_of_pos scale_pos] using hm
  have hpre1 : (fun x : ℝ => scale⁻¹*x) ⁻¹' Ioc 0 1 = Ioc 0 scale := by
    ext x
    simp only [mem_preimage,mem_Ioc,inv_mul_eq_div]
    rw [lt_div_iff₀ scale_pos, div_le_iff₀ scale_pos]
    simp
  have hpre2 : (fun x : ℝ => scale⁻¹*x) ⁻¹' Ioo 0 (1/2:ℝ) = Ioo 0 Real.pi := by
    ext x
    simp only [mem_preimage,mem_Ioo,inv_mul_eq_div]
    rw [lt_div_iff₀ scale_pos, div_lt_iff₀ scale_pos]
    simp [scale]
  unfold Friedrichs.MixedSpatial.coordinateMeasure coordinateMeasure
  split_ifs
  · rw [show Ioc 0 (2*Real.pi) = (fun x : ℝ => scale⁻¹*x) ⁻¹' Ioc 0 1 from hpre1.symm,
      ← Measure.restrict_map (measurable_const_mul _) measurableSet_Ioc, hv,
      Measure.restrict_smul]
  · rw [← hpre2, ← Measure.restrict_map (measurable_const_mul _) measurableSet_Ioo,
      hv, Measure.restrict_smul]

lemma map_spatial {d : ℕ} (α : MultiIndex d) :
    (Friedrichs.MixedSpatial.spatialMeasure α).map down =
      ENNReal.ofReal (scale^d) • spatialMeasure α := by
  haveI (i : Fin d) : IsFiniteMeasure (ENNReal.ofReal scale • coordinateMeasure (α i)) :=
    ⟨by simp [Measure.smul_apply, ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) (measure_lt_top _ _)]⟩
  unfold Friedrichs.MixedSpatial.spatialMeasure spatialMeasure down
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul _).aemeasurable)]
  simp_rw [map_coordinate]
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp [ENNReal.ofReal_pow scale_pos.le]

end BecknerOnofri.Paper2.Physical
