module

public import BecknerOnofri.EntropyHeatIntegerWeights
public import BecknerOnofri.EntropyHeatWeightedBlocks

@[expose] public section

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

def weightedBlockOfRows (b : PanelBlock) (hb : b.check = true) (ps : List IntegerPanel)
    (halign : b.panels.map EndpointPanel.rationalPanel = ps.map IntegerPanel.rationalPanel)
    (rows : List (ℤ × ℤ))
    (hrows : rows.all (fun z => decide (integerPanelWeight ps z.1 = z.2)) = true)
    (i : Fin rows.length) : WeightedPanelBlock ((rows[i].1 : ℚ)/panelScale) where
  certificate := ⟨b, hb⟩
  upper := (rows[i].2 : ℚ)/(720*(panelScale : ℚ)^7)
  weight_le := by
    apply le_of_eq
    rw [b.weight_eq_integer ps halign]
    have h := List.all_eq_true.mp hrows _ (List.getElem_mem i.isLt)
    have he : integerPanelWeight ps rows[i].1 = rows[i].2 := of_decide_eq_true h
    rw [he]

#print axioms weightedBlockOfRows
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
