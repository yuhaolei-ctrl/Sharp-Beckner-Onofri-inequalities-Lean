import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0218
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0218
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1744 : minorantGammaCheck GammaPanel1744.certificate 1472=true := by decide +kernel
noncomputable def cell1744 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1744.certificate 1472 accepted1744
theorem accepted1745 : minorantGammaCheck GammaPanel1745.certificate 1472=true := by decide +kernel
noncomputable def cell1745 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1745.certificate 1472 accepted1745
theorem accepted1746 : minorantGammaCheck GammaPanel1746.certificate 1472=true := by decide +kernel
noncomputable def cell1746 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1746.certificate 1472 accepted1746
theorem accepted1747 : minorantGammaCheck GammaPanel1747.certificate 1472=true := by decide +kernel
noncomputable def cell1747 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1747.certificate 1472 accepted1747
theorem accepted1748 : minorantGammaCheck GammaPanel1748.certificate 1472=true := by decide +kernel
noncomputable def cell1748 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1748.certificate 1472 accepted1748
theorem accepted1749 : minorantGammaCheck GammaPanel1749.certificate 1472=true := by decide +kernel
noncomputable def cell1749 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1749.certificate 1472 accepted1749
theorem accepted1750 : minorantGammaCheck GammaPanel1750.certificate 1472=true := by decide +kernel
noncomputable def cell1750 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1750.certificate 1472 accepted1750
theorem accepted1751 : minorantGammaCheck GammaPanel1751.certificate 1472=true := by decide +kernel
noncomputable def cell1751 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1751.certificate 1472 accepted1751
noncomputable def cells : List CertifiedMinorantCell := [cell1744, cell1745, cell1746, cell1747, cell1748, cell1749, cell1750, cell1751]
theorem chainAccepted : minorantChainCheck (4333/5000) (4337/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4333/5000) (4337/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0218
