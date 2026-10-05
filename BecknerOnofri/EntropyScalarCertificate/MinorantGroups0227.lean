import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0227
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0227
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1816 : minorantGammaCheck GammaPanel1816.certificate 1472=true := by decide +kernel
noncomputable def cell1816 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1816.certificate 1472 accepted1816
theorem accepted1817 : minorantGammaCheck GammaPanel1817.certificate 1472=true := by decide +kernel
noncomputable def cell1817 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1817.certificate 1472 accepted1817
theorem accepted1818 : minorantGammaCheck GammaPanel1818.certificate 1472=true := by decide +kernel
noncomputable def cell1818 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1818.certificate 1472 accepted1818
theorem accepted1819 : minorantGammaCheck GammaPanel1819.certificate 1472=true := by decide +kernel
noncomputable def cell1819 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1819.certificate 1472 accepted1819
theorem accepted1820 : minorantGammaCheck GammaPanel1820.certificate 1472=true := by decide +kernel
noncomputable def cell1820 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1820.certificate 1472 accepted1820
theorem accepted1821 : minorantGammaCheck GammaPanel1821.certificate 1472=true := by decide +kernel
noncomputable def cell1821 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1821.certificate 1472 accepted1821
theorem accepted1822 : minorantGammaCheck GammaPanel1822.certificate 1472=true := by decide +kernel
noncomputable def cell1822 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1822.certificate 1472 accepted1822
theorem accepted1823 : minorantGammaCheck GammaPanel1823.certificate 1472=true := by decide +kernel
noncomputable def cell1823 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1823.certificate 1472 accepted1823
noncomputable def cells : List CertifiedMinorantCell := [cell1816, cell1817, cell1818, cell1819, cell1820, cell1821, cell1822, cell1823]
theorem chainAccepted : minorantChainCheck (4369/5000) (4373/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4369/5000) (4373/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0227
