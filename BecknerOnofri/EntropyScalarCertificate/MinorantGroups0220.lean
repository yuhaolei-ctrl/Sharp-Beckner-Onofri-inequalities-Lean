import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0220
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0220
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1760 : minorantGammaCheck GammaPanel1760.certificate 1472=true := by decide +kernel
noncomputable def cell1760 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1760.certificate 1472 accepted1760
theorem accepted1761 : minorantGammaCheck GammaPanel1761.certificate 1472=true := by decide +kernel
noncomputable def cell1761 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1761.certificate 1472 accepted1761
theorem accepted1762 : minorantGammaCheck GammaPanel1762.certificate 1472=true := by decide +kernel
noncomputable def cell1762 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1762.certificate 1472 accepted1762
theorem accepted1763 : minorantGammaCheck GammaPanel1763.certificate 1472=true := by decide +kernel
noncomputable def cell1763 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1763.certificate 1472 accepted1763
theorem accepted1764 : minorantGammaCheck GammaPanel1764.certificate 1472=true := by decide +kernel
noncomputable def cell1764 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1764.certificate 1472 accepted1764
theorem accepted1765 : minorantGammaCheck GammaPanel1765.certificate 1472=true := by decide +kernel
noncomputable def cell1765 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1765.certificate 1472 accepted1765
theorem accepted1766 : minorantGammaCheck GammaPanel1766.certificate 1472=true := by decide +kernel
noncomputable def cell1766 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1766.certificate 1472 accepted1766
theorem accepted1767 : minorantGammaCheck GammaPanel1767.certificate 1472=true := by decide +kernel
noncomputable def cell1767 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1767.certificate 1472 accepted1767
noncomputable def cells : List CertifiedMinorantCell := [cell1760, cell1761, cell1762, cell1763, cell1764, cell1765, cell1766, cell1767]
theorem chainAccepted : minorantChainCheck (4341/5000) (869/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4341/5000) (869/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0220
