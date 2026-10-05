module

public import BecknerOnofri.EntropyHeatWeightedBlocks

@[expose] public section

/-! Compact proof-carrying segments for assembling the already checked heat
panels. Each segment stores a rational upper bound and an opaque analytic
proof, so later rows do not elaborate one enormous dependent panel list. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate
open MeasureTheory Set

structure WeightedSegment (ζ : ℚ) where
  left : ℚ
  right : ℚ
  upper : ℚ
  ordered : 0<left ∧ left≤right
  bound : ∀ η : ℝ, (ζ : ℝ)≤η →
    (1/120 : ℝ)*(∫ s in (left : ℝ)..(right : ℝ),
      (max (s-η) 0)^5*heatComplement s) ≤ (upper : ℝ)

def segmentOfBlocks {ζ a b U : ℚ} (ps : List (WeightedPanelBlock ζ))
    (hc : blockChainCheck a b (ps.map WeightedPanelBlock.certificate)=true)
    (ha : 0<a) (hU : weightedTotal ps=U) : WeightedSegment ζ where
  left := a
  right := b
  upper := U
  ordered := ⟨ha,blockChainCheck_le hc⟩
  bound := by
    intro η hζη
    have h := blockChain_integral_bound (ps.map WeightedPanelBlock.certificate) hc ha η ζ hζη
    have hw := (Rat.cast_le (K := ℝ)).mpr (checkedWeight_le_total ps)
    rw [hU] at hw
    exact h.trans hw

def segmentChainCheck {ζ : ℚ} (a b : ℚ) : List (WeightedSegment ζ) → Bool
  | [] => decide (a=b)
  | p::ps => decide (a=p.left) && segmentChainCheck p.right b ps

def segmentTotal {ζ : ℚ} (ps : List (WeightedSegment ζ)) : ℚ :=
  (ps.map WeightedSegment.upper).sum

theorem segmentChain_le {ζ a b : ℚ} {ps : List (WeightedSegment ζ)}
    (hc : segmentChainCheck a b ps=true) : a≤b := by
  induction ps generalizing a with
  | nil => exact (of_decide_eq_true hc : a=b).le
  | cons p ps ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hc
    exact (of_decide_eq_true ha : a=p.left).le.trans (p.ordered.2.trans (ih hb))

theorem segment_integral_bound {ζ : ℚ} (ps : List (WeightedSegment ζ)) {a b : ℚ}
    (hc : segmentChainCheck a b ps=true) (ha : 0<a) (η : ℝ) (hζη : (ζ : ℝ)≤η) :
    (1/120 : ℝ)*(∫ s in (a : ℝ)..(b : ℝ), (max (s-η) 0)^5*heatComplement s) ≤
      (segmentTotal ps : ℝ) := by
  induction ps generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true hc
    subst a
    simp [segmentTotal]
  | cons p ps ih =>
    obtain ⟨hp,hr⟩ := Bool.and_eq_true_iff.mp hc
    have he : a=p.left := of_decide_eq_true hp
    subst a
    have hb : 0<p.right := ha.trans_le p.ordered.2
    have hend : p.right≤b := segmentChain_le hr
    have hi1 := heat_panel_integrable (v := (p.left : ℝ)) (w := (p.right : ℝ))
      (by exact_mod_cast ha) (by exact_mod_cast p.ordered.2) η
    have hi2 := heat_panel_integrable (v := (p.right : ℝ)) (w := (b : ℝ))
      (by exact_mod_cast hb) (by exact_mod_cast hend) η
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, mul_add]
    simpa only [segmentTotal, List.map_cons, List.sum_cons, Rat.cast_add] using
      add_le_add (p.bound η hζη) (ih hr hb)

theorem segments_heatIntegral_bound {ζ : ℚ} (ps : List (WeightedSegment ζ)) {a : ℚ}
    (hc : segmentChainCheck a 20 ps=true) (ha : 0<a) {η : ℝ}
    (haη : (a : ℝ)≤η) (hη20 : η≤20) (hζη : (ζ : ℝ)≤η) :
    heatIntegral η < (segmentTotal ps : ℝ)+667/(2*10^32) := by
  have ha' : (0 : ℝ)<a := by exact_mod_cast ha
  have hη := ha'.trans_le haη
  have hp := segment_integral_bound ps hc ha η hζη
  norm_num only [Rat.cast_ofNat] at hp
  rw [positive_mellin_interval ha' haη hη20] at hp
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (heat_integrable hη) hη20
  have ht := heat_integral_beyond_twenty hη hη20
  unfold heatIntegral
  linarith

#print axioms segments_heatIntegral_bound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
