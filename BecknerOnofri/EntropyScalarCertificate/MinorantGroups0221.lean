import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0221
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0221
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1768 : minorantGammaCheck GammaPanel1768.certificate 1472=true := by decide +kernel
noncomputable def cell1768 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1768.certificate 1472 accepted1768
theorem accepted1769 : minorantGammaCheck GammaPanel1769.certificate 1472=true := by decide +kernel
noncomputable def cell1769 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1769.certificate 1472 accepted1769
theorem accepted1770 : minorantGammaCheck GammaPanel1770.certificate 1472=true := by decide +kernel
noncomputable def cell1770 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1770.certificate 1472 accepted1770
theorem accepted1771 : minorantGammaCheck GammaPanel1771.certificate 1472=true := by decide +kernel
noncomputable def cell1771 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1771.certificate 1472 accepted1771
theorem accepted1772 : minorantGammaCheck GammaPanel1772.certificate 1472=true := by decide +kernel
noncomputable def cell1772 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1772.certificate 1472 accepted1772
theorem accepted1773 : minorantGammaCheck GammaPanel1773.certificate 1472=true := by decide +kernel
noncomputable def cell1773 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1773.certificate 1472 accepted1773
theorem accepted1774 : minorantGammaCheck GammaPanel1774.certificate 1472=true := by decide +kernel
noncomputable def cell1774 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1774.certificate 1472 accepted1774
theorem accepted1775 : minorantGammaCheck GammaPanel1775.certificate 1472=true := by decide +kernel
noncomputable def cell1775 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1775.certificate 1472 accepted1775
noncomputable def cells : List CertifiedMinorantCell := [cell1768, cell1769, cell1770, cell1771, cell1772, cell1773, cell1774, cell1775]
theorem chainAccepted : minorantChainCheck (869/1000) (4349/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (869/1000) (4349/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0221
