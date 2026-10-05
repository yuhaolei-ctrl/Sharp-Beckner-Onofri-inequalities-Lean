import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0219
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0219
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1752 : minorantGammaCheck GammaPanel1752.certificate 1472=true := by decide +kernel
noncomputable def cell1752 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1752.certificate 1472 accepted1752
theorem accepted1753 : minorantGammaCheck GammaPanel1753.certificate 1472=true := by decide +kernel
noncomputable def cell1753 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1753.certificate 1472 accepted1753
theorem accepted1754 : minorantGammaCheck GammaPanel1754.certificate 1472=true := by decide +kernel
noncomputable def cell1754 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1754.certificate 1472 accepted1754
theorem accepted1755 : minorantGammaCheck GammaPanel1755.certificate 1472=true := by decide +kernel
noncomputable def cell1755 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1755.certificate 1472 accepted1755
theorem accepted1756 : minorantGammaCheck GammaPanel1756.certificate 1472=true := by decide +kernel
noncomputable def cell1756 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1756.certificate 1472 accepted1756
theorem accepted1757 : minorantGammaCheck GammaPanel1757.certificate 1472=true := by decide +kernel
noncomputable def cell1757 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1757.certificate 1472 accepted1757
theorem accepted1758 : minorantGammaCheck GammaPanel1758.certificate 1472=true := by decide +kernel
noncomputable def cell1758 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1758.certificate 1472 accepted1758
theorem accepted1759 : minorantGammaCheck GammaPanel1759.certificate 1472=true := by decide +kernel
noncomputable def cell1759 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1759.certificate 1472 accepted1759
noncomputable def cells : List CertifiedMinorantCell := [cell1752, cell1753, cell1754, cell1755, cell1756, cell1757, cell1758, cell1759]
theorem chainAccepted : minorantChainCheck (4337/5000) (4341/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4337/5000) (4341/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0219
