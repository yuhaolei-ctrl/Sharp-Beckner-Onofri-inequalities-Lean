module

public import BecknerOnofri.EntropyHeatCheckedPanels

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

structure CheckedPanelBlock where
  block : PanelBlock
  accepted : block.check = true

theorem CheckedPanelBlock.ordered (b : CheckedPanelBlock) :
    0 < b.block.left ∧ b.block.left ≤ b.block.right := by
  have h : 0 < b.block.left ∧ b.block.panels.all (fun p => p.endpoint.check) = true ∧
      chainCheck b.block.left b.block.right (b.block.panels.map EndpointPanel.rationalPanel) = true := by
    simpa only [PanelBlock.check, Bool.and_eq_true_iff, decide_eq_true_eq] using b.accepted
  exact ⟨h.1, chainCheck_le h.2.2⟩

def blockChainCheck (a b : ℚ) : List CheckedPanelBlock → Bool
  | [] => decide (a=b)
  | p::ps => decide (a=p.block.left) && blockChainCheck p.block.right b ps

def blockChainWeight (ps : List CheckedPanelBlock) (ζ : ℚ) : ℚ :=
  (ps.map (fun p => p.block.weight ζ)).sum

theorem blockChainCheck_le {a b : ℚ} {ps : List CheckedPanelBlock}
    (h : blockChainCheck a b ps = true) : a ≤ b := by
  induction ps generalizing a with
  | nil => have he : a=b := of_decide_eq_true h; exact he.le
  | cons p ps ih =>
    obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp h
    have he : a=p.block.left := of_decide_eq_true hp
    exact he.le.trans (p.ordered.2.trans (ih hr))

theorem blockChain_integral_bound (ps : List CheckedPanelBlock) {a b : ℚ}
    (hc : blockChainCheck a b ps = true) (ha : 0 < a)
    (η : ℝ) (ζ : ℚ) (hζη : (ζ : ℝ) ≤ η) :
    (1/120 : ℝ)*(∫ s in (a : ℝ)..(b : ℝ), (max (s-η) 0)^5*heatComplement s) ≤
      (blockChainWeight ps ζ : ℝ) := by
  induction ps generalizing a with
  | nil =>
    have he : a=b := of_decide_eq_true hc
    subst a
    simp [blockChainWeight]
  | cons p ps ih =>
    obtain ⟨hp, hr⟩ := Bool.and_eq_true_iff.mp hc
    have he : a=p.block.left := of_decide_eq_true hp
    subst a
    have hab := p.ordered.2
    have hb : 0 < p.block.right := ha.trans_le hab
    have hend : p.block.right ≤ b := blockChainCheck_le hr
    have hi1 := heat_panel_integrable (v := (p.block.left : ℝ)) (w := (p.block.right : ℝ))
      (by exact_mod_cast ha) (by exact_mod_cast hab) η
    have hi2 := heat_panel_integrable (v := (p.block.right : ℝ)) (w := (b : ℝ))
      (by exact_mod_cast hb) (by exact_mod_cast hend) η
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, mul_add]
    have hfirst := p.block.bound p.accepted η ζ hζη
    have hrest := ih hr hb
    simpa only [blockChainWeight, List.map_cons, List.sum_cons, Rat.cast_add] using add_le_add hfirst hrest

/-- Soundness of a complete, linked, kernel checked collection of heat panels. -/
theorem checked_heatIntegral_bound (ps : List CheckedPanelBlock) {a : ℚ}
    (hc : blockChainCheck a 20 ps = true) (ha : 0 < a)
    {η : ℝ} {ζ : ℚ} (haη : (a : ℝ) ≤ η) (hη20 : η ≤ 20) (hζη : (ζ : ℝ) ≤ η) :
    heatIntegral η < (blockChainWeight ps ζ : ℝ) + 667/(2*10^32) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hη := ha'.trans_le haη
  have hp := blockChain_integral_bound ps hc ha η ζ hζη
  norm_num only [Rat.cast_ofNat] at hp
  rw [positive_mellin_interval ha' haη hη20] at hp
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (heat_integrable hη) hη20
  have ht := heat_integral_beyond_twenty hη hη20
  unfold heatIntegral
  linarith

#print axioms checked_heatIntegral_bound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
