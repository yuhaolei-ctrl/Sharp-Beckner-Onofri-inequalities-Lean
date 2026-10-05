module

public import BecknerOnofri.EntropyHeatBlockChain

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

structure WeightedPanelBlock (ζ : ℚ) where
  certificate : CheckedPanelBlock
  upper : ℚ
  weight_le : certificate.block.weight ζ ≤ upper

def weightedTotal {ζ : ℚ} (ps : List (WeightedPanelBlock ζ)) : ℚ :=
  (ps.map WeightedPanelBlock.upper).sum

theorem checkedWeight_le_total {ζ : ℚ} (ps : List (WeightedPanelBlock ζ)) :
    blockChainWeight (ps.map WeightedPanelBlock.certificate) ζ ≤ weightedTotal ps := by
  induction ps with
  | nil => simp [blockChainWeight, weightedTotal]
  | cons p ps ih =>
    simpa only [blockChainWeight, weightedTotal, List.map_cons, List.sum_cons] using
      add_le_add p.weight_le ih

theorem weighted_heatIntegral_bound {ζ : ℚ} (ps : List (WeightedPanelBlock ζ)) {a : ℚ}
    (hc : blockChainCheck a 20 (ps.map WeightedPanelBlock.certificate) = true) (ha : 0 < a)
    {η : ℝ} (haη : (a : ℝ) ≤ η) (hη20 : η ≤ 20) (hζη : (ζ : ℝ) ≤ η) :
    heatIntegral η < (weightedTotal ps : ℝ) + 667/(2*10^32) := by
  have h := checked_heatIntegral_bound (ps.map WeightedPanelBlock.certificate) hc ha haη hη20 hζη
  have hw := (Rat.cast_le (K := ℝ)).mpr (checkedWeight_le_total ps)
  linarith

#print axioms weighted_heatIntegral_bound
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
