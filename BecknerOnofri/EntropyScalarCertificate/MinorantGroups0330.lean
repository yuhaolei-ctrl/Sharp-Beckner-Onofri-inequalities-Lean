import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0330
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0330
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2640 : minorantGammaCheck GammaPanel2640.certificate 1621=true := by decide +kernel
noncomputable def cell2640 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2640.certificate 1621 accepted2640
theorem accepted2641 : minorantGammaCheck GammaPanel2641.certificate 1621=true := by decide +kernel
noncomputable def cell2641 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2641.certificate 1621 accepted2641
theorem accepted2642 : minorantGammaCheck GammaPanel2642.certificate 1621=true := by decide +kernel
noncomputable def cell2642 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2642.certificate 1621 accepted2642
theorem accepted2643 : minorantGammaCheck GammaPanel2643.certificate 1621=true := by decide +kernel
noncomputable def cell2643 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2643.certificate 1621 accepted2643
theorem accepted2644 : minorantGammaCheck GammaPanel2644.certificate 1621=true := by decide +kernel
noncomputable def cell2644 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2644.certificate 1621 accepted2644
theorem accepted2645 : minorantGammaCheck GammaPanel2645.certificate 1621=true := by decide +kernel
noncomputable def cell2645 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2645.certificate 1621 accepted2645
theorem accepted2646 : minorantGammaCheck GammaPanel2646.certificate 1621=true := by decide +kernel
noncomputable def cell2646 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2646.certificate 1621 accepted2646
theorem accepted2647 : minorantGammaCheck GammaPanel2647.certificate 1621=true := by decide +kernel
noncomputable def cell2647 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2647.certificate 1621 accepted2647
noncomputable def cells : List CertifiedMinorantCell := [cell2640, cell2641, cell2642, cell2643, cell2644, cell2645, cell2646, cell2647]
theorem chainAccepted : minorantChainCheck (24881/25000) (4977/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24881/25000) (4977/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0330
