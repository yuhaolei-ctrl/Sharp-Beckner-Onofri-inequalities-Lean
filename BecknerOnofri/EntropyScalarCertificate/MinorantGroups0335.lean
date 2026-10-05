import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0335
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0335
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2680 : minorantGammaCheck GammaPanel2680.certificate 1621=true := by decide +kernel
noncomputable def cell2680 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2680.certificate 1621 accepted2680
theorem accepted2681 : minorantGammaCheck GammaPanel2681.certificate 1621=true := by decide +kernel
noncomputable def cell2681 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2681.certificate 1621 accepted2681
theorem accepted2682 : minorantGammaCheck GammaPanel2682.certificate 1621=true := by decide +kernel
noncomputable def cell2682 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2682.certificate 1621 accepted2682
theorem accepted2683 : minorantGammaCheck GammaPanel2683.certificate 1621=true := by decide +kernel
noncomputable def cell2683 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2683.certificate 1621 accepted2683
theorem accepted2684 : minorantGammaCheck GammaPanel2684.certificate 1621=true := by decide +kernel
noncomputable def cell2684 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2684.certificate 1621 accepted2684
theorem accepted2685 : minorantGammaCheck GammaPanel2685.certificate 1621=true := by decide +kernel
noncomputable def cell2685 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2685.certificate 1621 accepted2685
theorem accepted2686 : minorantGammaCheck GammaPanel2686.certificate 1621=true := by decide +kernel
noncomputable def cell2686 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2686.certificate 1621 accepted2686
theorem accepted2687 : minorantGammaCheck GammaPanel2687.certificate 1621=true := by decide +kernel
noncomputable def cell2687 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2687.certificate 1621 accepted2687
noncomputable def cells : List CertifiedMinorantCell := [cell2680, cell2681, cell2682, cell2683, cell2684, cell2685, cell2686, cell2687]
theorem chainAccepted : minorantChainCheck (24901/25000) (4981/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24901/25000) (4981/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0335
