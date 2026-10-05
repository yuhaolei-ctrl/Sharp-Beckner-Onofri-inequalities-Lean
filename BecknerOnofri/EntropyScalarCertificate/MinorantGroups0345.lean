module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0345

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0345
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2760 : minorantGammaCheck GammaPanel2760.certificate 1621=true := by decide +kernel
noncomputable def cell2760 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2760.certificate 1621 accepted2760
theorem accepted2761 : minorantGammaCheck GammaPanel2761.certificate 1621=true := by decide +kernel
noncomputable def cell2761 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2761.certificate 1621 accepted2761
theorem accepted2762 : minorantGammaCheck GammaPanel2762.certificate 1621=true := by decide +kernel
noncomputable def cell2762 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2762.certificate 1621 accepted2762
theorem accepted2763 : minorantGammaCheck GammaPanel2763.certificate 1621=true := by decide +kernel
noncomputable def cell2763 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2763.certificate 1621 accepted2763
theorem accepted2764 : minorantGammaCheck GammaPanel2764.certificate 1621=true := by decide +kernel
noncomputable def cell2764 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2764.certificate 1621 accepted2764
theorem accepted2765 : minorantGammaCheck GammaPanel2765.certificate 1621=true := by decide +kernel
noncomputable def cell2765 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2765.certificate 1621 accepted2765
theorem accepted2766 : minorantGammaCheck GammaPanel2766.certificate 1621=true := by decide +kernel
noncomputable def cell2766 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2766.certificate 1621 accepted2766
theorem accepted2767 : minorantGammaCheck GammaPanel2767.certificate 1621=true := by decide +kernel
noncomputable def cell2767 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2767.certificate 1621 accepted2767
noncomputable def cells : List CertifiedMinorantCell := [cell2760, cell2761, cell2762, cell2763, cell2764, cell2765, cell2766, cell2767]
theorem chainAccepted : minorantChainCheck (24929/25000) (2493/2500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24929/25000) (2493/2500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0345
