import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0326
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0326
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2608 : minorantGammaCheck GammaPanel2608.certificate 1621=true := by decide +kernel
noncomputable def cell2608 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2608.certificate 1621 accepted2608
theorem accepted2609 : minorantGammaCheck GammaPanel2609.certificate 1621=true := by decide +kernel
noncomputable def cell2609 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2609.certificate 1621 accepted2609
theorem accepted2610 : minorantGammaCheck GammaPanel2610.certificate 1621=true := by decide +kernel
noncomputable def cell2610 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2610.certificate 1621 accepted2610
theorem accepted2611 : minorantGammaCheck GammaPanel2611.certificate 1621=true := by decide +kernel
noncomputable def cell2611 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2611.certificate 1621 accepted2611
theorem accepted2612 : minorantGammaCheck GammaPanel2612.certificate 1621=true := by decide +kernel
noncomputable def cell2612 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2612.certificate 1621 accepted2612
theorem accepted2613 : minorantGammaCheck GammaPanel2613.certificate 1621=true := by decide +kernel
noncomputable def cell2613 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2613.certificate 1621 accepted2613
theorem accepted2614 : minorantGammaCheck GammaPanel2614.certificate 1621=true := by decide +kernel
noncomputable def cell2614 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2614.certificate 1621 accepted2614
theorem accepted2615 : minorantGammaCheck GammaPanel2615.certificate 1621=true := by decide +kernel
noncomputable def cell2615 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2615.certificate 1621 accepted2615
noncomputable def cells : List CertifiedMinorantCell := [cell2608, cell2609, cell2610, cell2611, cell2612, cell2613, cell2614, cell2615]
theorem chainAccepted : minorantChainCheck (4973/5000) (24869/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4973/5000) (24869/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0326
