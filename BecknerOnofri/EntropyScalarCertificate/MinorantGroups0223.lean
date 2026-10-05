import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0223
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0223
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1784 : minorantGammaCheck GammaPanel1784.certificate 1472=true := by decide +kernel
noncomputable def cell1784 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1784.certificate 1472 accepted1784
theorem accepted1785 : minorantGammaCheck GammaPanel1785.certificate 1472=true := by decide +kernel
noncomputable def cell1785 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1785.certificate 1472 accepted1785
theorem accepted1786 : minorantGammaCheck GammaPanel1786.certificate 1472=true := by decide +kernel
noncomputable def cell1786 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1786.certificate 1472 accepted1786
theorem accepted1787 : minorantGammaCheck GammaPanel1787.certificate 1472=true := by decide +kernel
noncomputable def cell1787 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1787.certificate 1472 accepted1787
theorem accepted1788 : minorantGammaCheck GammaPanel1788.certificate 1472=true := by decide +kernel
noncomputable def cell1788 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1788.certificate 1472 accepted1788
theorem accepted1789 : minorantGammaCheck GammaPanel1789.certificate 1472=true := by decide +kernel
noncomputable def cell1789 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1789.certificate 1472 accepted1789
theorem accepted1790 : minorantGammaCheck GammaPanel1790.certificate 1472=true := by decide +kernel
noncomputable def cell1790 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1790.certificate 1472 accepted1790
theorem accepted1791 : minorantGammaCheck GammaPanel1791.certificate 1472=true := by decide +kernel
noncomputable def cell1791 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1791.certificate 1472 accepted1791
noncomputable def cells : List CertifiedMinorantCell := [cell1784, cell1785, cell1786, cell1787, cell1788, cell1789, cell1790, cell1791]
theorem chainAccepted : minorantChainCheck (4353/5000) (4357/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4353/5000) (4357/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0223
