import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0346
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0346
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2768 : minorantGammaCheck GammaPanel2768.certificate 1621=true := by decide +kernel
noncomputable def cell2768 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2768.certificate 1621 accepted2768
theorem accepted2769 : minorantGammaCheck GammaPanel2769.certificate 1621=true := by decide +kernel
noncomputable def cell2769 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2769.certificate 1621 accepted2769
theorem accepted2770 : minorantGammaCheck GammaPanel2770.certificate 1621=true := by decide +kernel
noncomputable def cell2770 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2770.certificate 1621 accepted2770
theorem accepted2771 : minorantGammaCheck GammaPanel2771.certificate 1621=true := by decide +kernel
noncomputable def cell2771 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2771.certificate 1621 accepted2771
theorem accepted2772 : minorantGammaCheck GammaPanel2772.certificate 1621=true := by decide +kernel
noncomputable def cell2772 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2772.certificate 1621 accepted2772
theorem accepted2773 : minorantGammaCheck GammaPanel2773.certificate 1621=true := by decide +kernel
noncomputable def cell2773 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2773.certificate 1621 accepted2773
theorem accepted2774 : minorantGammaCheck GammaPanel2774.certificate 1621=true := by decide +kernel
noncomputable def cell2774 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2774.certificate 1621 accepted2774
theorem accepted2775 : minorantGammaCheck GammaPanel2775.certificate 1621=true := by decide +kernel
noncomputable def cell2775 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2775.certificate 1621 accepted2775
noncomputable def cells : List CertifiedMinorantCell := [cell2768, cell2769, cell2770, cell2771, cell2772, cell2773, cell2774, cell2775]
theorem chainAccepted : minorantChainCheck (2493/2500) (24931/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (2493/2500) (24931/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0346
