module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0332

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0332
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2656 : minorantGammaCheck GammaPanel2656.certificate 1621=true := by decide +kernel
noncomputable def cell2656 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2656.certificate 1621 accepted2656
theorem accepted2657 : minorantGammaCheck GammaPanel2657.certificate 1621=true := by decide +kernel
noncomputable def cell2657 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2657.certificate 1621 accepted2657
theorem accepted2658 : minorantGammaCheck GammaPanel2658.certificate 1621=true := by decide +kernel
noncomputable def cell2658 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2658.certificate 1621 accepted2658
theorem accepted2659 : minorantGammaCheck GammaPanel2659.certificate 1621=true := by decide +kernel
noncomputable def cell2659 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2659.certificate 1621 accepted2659
theorem accepted2660 : minorantGammaCheck GammaPanel2660.certificate 1621=true := by decide +kernel
noncomputable def cell2660 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2660.certificate 1621 accepted2660
theorem accepted2661 : minorantGammaCheck GammaPanel2661.certificate 1621=true := by decide +kernel
noncomputable def cell2661 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2661.certificate 1621 accepted2661
theorem accepted2662 : minorantGammaCheck GammaPanel2662.certificate 1621=true := by decide +kernel
noncomputable def cell2662 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2662.certificate 1621 accepted2662
theorem accepted2663 : minorantGammaCheck GammaPanel2663.certificate 1621=true := by decide +kernel
noncomputable def cell2663 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2663.certificate 1621 accepted2663
noncomputable def cells : List CertifiedMinorantCell := [cell2656, cell2657, cell2658, cell2659, cell2660, cell2661, cell2662, cell2663]
theorem chainAccepted : minorantChainCheck (24889/25000) (24893/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24889/25000) (24893/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0332
