import BecknerOnofri.EntropyHeatEndpointBlocks
import BecknerOnofri.EntropyHeatPanelChain

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

structure EndpointPanel where
  endpoint : Endpoint
  right : ℚ

def EndpointPanel.rationalPanel (p : EndpointPanel) : RationalPanel :=
  ⟨p.endpoint.point, p.right, p.endpoint.upper⟩

structure PanelBlock where
  left : ℚ
  right : ℚ
  panels : List EndpointPanel

def PanelBlock.check (b : PanelBlock) : Bool :=
  decide (0 < b.left) && ((b.panels.all (fun p => p.endpoint.check)) &&
    chainCheck b.left b.right (b.panels.map EndpointPanel.rationalPanel))

def PanelBlock.weight (b : PanelBlock) (ζ : ℚ) : ℚ :=
  (b.panels.map (fun p => p.rationalPanel.weight ζ)).sum

theorem PanelBlock.bound (b : PanelBlock) (hc : b.check = true)
    (η : ℝ) (ζ : ℚ) (hζη : (ζ : ℝ) ≤ η) :
    (1/120 : ℝ)*(∫ s in (b.left : ℝ)..(b.right : ℝ),
      (max (s-η) 0)^5*heatComplement s) ≤ (b.weight ζ : ℝ) := by
  have h : 0 < b.left ∧ b.panels.all (fun p => p.endpoint.check) = true ∧
      chainCheck b.left b.right (b.panels.map EndpointPanel.rationalPanel) = true := by
    simpa only [PanelBlock.check, Bool.and_eq_true_iff, decide_eq_true_eq] using hc
  have hu : ∀ p ∈ b.panels.map EndpointPanel.rationalPanel,
      heatComplement (p.left : ℝ) ≤ (p.upper : ℝ) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact q.endpoint.sound (List.all_eq_true.mp h.2.1 q hq)
  have hh := chain_integral_bound (b.panels.map EndpointPanel.rationalPanel) h.2.2 h.1 η ζ hζη hu
  simpa only [PanelBlock.weight, List.map_map, Function.comp_def] using hh

#print axioms PanelBlock.bound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
