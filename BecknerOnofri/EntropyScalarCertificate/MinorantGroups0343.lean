module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0343

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0343
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2744 : minorantGammaCheck GammaPanel2744.certificate 1621=true := by decide +kernel
noncomputable def cell2744 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2744.certificate 1621 accepted2744
theorem accepted2745 : minorantGammaCheck GammaPanel2745.certificate 1621=true := by decide +kernel
noncomputable def cell2745 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2745.certificate 1621 accepted2745
theorem accepted2746 : minorantGammaCheck GammaPanel2746.certificate 1621=true := by decide +kernel
noncomputable def cell2746 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2746.certificate 1621 accepted2746
theorem accepted2747 : minorantGammaCheck GammaPanel2747.certificate 1621=true := by decide +kernel
noncomputable def cell2747 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2747.certificate 1621 accepted2747
theorem accepted2748 : minorantGammaCheck GammaPanel2748.certificate 1621=true := by decide +kernel
noncomputable def cell2748 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2748.certificate 1621 accepted2748
theorem accepted2749 : minorantGammaCheck GammaPanel2749.certificate 1621=true := by decide +kernel
noncomputable def cell2749 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2749.certificate 1621 accepted2749
theorem accepted2750 : minorantGammaCheck GammaPanel2750.certificate 1621=true := by decide +kernel
noncomputable def cell2750 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2750.certificate 1621 accepted2750
theorem accepted2751 : minorantGammaCheck GammaPanel2751.certificate 1621=true := by decide +kernel
noncomputable def cell2751 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2751.certificate 1621 accepted2751
noncomputable def cells : List CertifiedMinorantCell := [cell2744, cell2745, cell2746, cell2747, cell2748, cell2749, cell2750, cell2751]
theorem chainAccepted : minorantChainCheck (24927/25000) (3116/3125) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24927/25000) (3116/3125) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0343
