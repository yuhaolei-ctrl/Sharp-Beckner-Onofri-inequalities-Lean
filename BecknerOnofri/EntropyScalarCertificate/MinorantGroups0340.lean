import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0340
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0340
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2720 : minorantGammaCheck GammaPanel2720.certificate 1621=true := by decide +kernel
noncomputable def cell2720 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2720.certificate 1621 accepted2720
theorem accepted2721 : minorantGammaCheck GammaPanel2721.certificate 1621=true := by decide +kernel
noncomputable def cell2721 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2721.certificate 1621 accepted2721
theorem accepted2722 : minorantGammaCheck GammaPanel2722.certificate 1621=true := by decide +kernel
noncomputable def cell2722 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2722.certificate 1621 accepted2722
theorem accepted2723 : minorantGammaCheck GammaPanel2723.certificate 1621=true := by decide +kernel
noncomputable def cell2723 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2723.certificate 1621 accepted2723
theorem accepted2724 : minorantGammaCheck GammaPanel2724.certificate 1621=true := by decide +kernel
noncomputable def cell2724 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2724.certificate 1621 accepted2724
theorem accepted2725 : minorantGammaCheck GammaPanel2725.certificate 1621=true := by decide +kernel
noncomputable def cell2725 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2725.certificate 1621 accepted2725
theorem accepted2726 : minorantGammaCheck GammaPanel2726.certificate 1621=true := by decide +kernel
noncomputable def cell2726 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2726.certificate 1621 accepted2726
theorem accepted2727 : minorantGammaCheck GammaPanel2727.certificate 1621=true := by decide +kernel
noncomputable def cell2727 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2727.certificate 1621 accepted2727
noncomputable def cells : List CertifiedMinorantCell := [cell2720, cell2721, cell2722, cell2723, cell2724, cell2725, cell2726, cell2727]
theorem chainAccepted : minorantChainCheck (24921/25000) (997/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24921/25000) (997/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0340
