module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0228

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0228
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1824 : minorantGammaCheck GammaPanel1824.certificate 1472=true := by decide +kernel
noncomputable def cell1824 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1824.certificate 1472 accepted1824
theorem accepted1825 : minorantGammaCheck GammaPanel1825.certificate 1472=true := by decide +kernel
noncomputable def cell1825 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1825.certificate 1472 accepted1825
theorem accepted1826 : minorantGammaCheck GammaPanel1826.certificate 1472=true := by decide +kernel
noncomputable def cell1826 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1826.certificate 1472 accepted1826
theorem accepted1827 : minorantGammaCheck GammaPanel1827.certificate 1472=true := by decide +kernel
noncomputable def cell1827 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1827.certificate 1472 accepted1827
theorem accepted1828 : minorantGammaCheck GammaPanel1828.certificate 1472=true := by decide +kernel
noncomputable def cell1828 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1828.certificate 1472 accepted1828
theorem accepted1829 : minorantGammaCheck GammaPanel1829.certificate 1473=true := by decide +kernel
noncomputable def cell1829 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1829.certificate 1473 accepted1829
theorem accepted1830 : minorantGammaCheck GammaPanel1830.certificate 1474=true := by decide +kernel
noncomputable def cell1830 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1830.certificate 1474 accepted1830
theorem accepted1831 : minorantGammaCheck GammaPanel1831.certificate 1475=true := by decide +kernel
noncomputable def cell1831 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1831.certificate 1475 accepted1831
noncomputable def cells : List CertifiedMinorantCell := [cell1824, cell1825, cell1826, cell1827, cell1828, cell1829, cell1830, cell1831]
theorem chainAccepted : minorantChainCheck (4373/5000) (877/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4373/5000) (877/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0228
