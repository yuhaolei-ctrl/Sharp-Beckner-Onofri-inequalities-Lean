import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0333
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0333
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2664 : minorantGammaCheck GammaPanel2664.certificate 1621=true := by decide +kernel
noncomputable def cell2664 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2664.certificate 1621 accepted2664
theorem accepted2665 : minorantGammaCheck GammaPanel2665.certificate 1621=true := by decide +kernel
noncomputable def cell2665 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2665.certificate 1621 accepted2665
theorem accepted2666 : minorantGammaCheck GammaPanel2666.certificate 1621=true := by decide +kernel
noncomputable def cell2666 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2666.certificate 1621 accepted2666
theorem accepted2667 : minorantGammaCheck GammaPanel2667.certificate 1621=true := by decide +kernel
noncomputable def cell2667 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2667.certificate 1621 accepted2667
theorem accepted2668 : minorantGammaCheck GammaPanel2668.certificate 1621=true := by decide +kernel
noncomputable def cell2668 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2668.certificate 1621 accepted2668
theorem accepted2669 : minorantGammaCheck GammaPanel2669.certificate 1621=true := by decide +kernel
noncomputable def cell2669 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2669.certificate 1621 accepted2669
theorem accepted2670 : minorantGammaCheck GammaPanel2670.certificate 1621=true := by decide +kernel
noncomputable def cell2670 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2670.certificate 1621 accepted2670
theorem accepted2671 : minorantGammaCheck GammaPanel2671.certificate 1621=true := by decide +kernel
noncomputable def cell2671 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2671.certificate 1621 accepted2671
noncomputable def cells : List CertifiedMinorantCell := [cell2664, cell2665, cell2666, cell2667, cell2668, cell2669, cell2670, cell2671]
theorem chainAccepted : minorantChainCheck (24893/25000) (24897/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24893/25000) (24897/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0333
