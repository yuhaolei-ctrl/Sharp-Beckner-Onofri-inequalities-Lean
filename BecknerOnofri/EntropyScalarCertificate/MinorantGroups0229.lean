module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0229

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0229
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1832 : minorantGammaCheck GammaPanel1832.certificate 1476=true := by decide +kernel
noncomputable def cell1832 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1832.certificate 1476 accepted1832
theorem accepted1833 : minorantGammaCheck GammaPanel1833.certificate 1477=true := by decide +kernel
noncomputable def cell1833 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1833.certificate 1477 accepted1833
theorem accepted1834 : minorantGammaCheck GammaPanel1834.certificate 1478=true := by decide +kernel
noncomputable def cell1834 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1834.certificate 1478 accepted1834
theorem accepted1835 : minorantGammaCheck GammaPanel1835.certificate 1479=true := by decide +kernel
noncomputable def cell1835 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1835.certificate 1479 accepted1835
theorem accepted1836 : minorantGammaCheck GammaPanel1836.certificate 1480=true := by decide +kernel
noncomputable def cell1836 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1836.certificate 1480 accepted1836
theorem accepted1837 : minorantGammaCheck GammaPanel1837.certificate 1481=true := by decide +kernel
noncomputable def cell1837 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1837.certificate 1481 accepted1837
theorem accepted1838 : minorantGammaCheck GammaPanel1838.certificate 1482=true := by decide +kernel
noncomputable def cell1838 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1838.certificate 1482 accepted1838
theorem accepted1839 : minorantGammaCheck GammaPanel1839.certificate 1483=true := by decide +kernel
noncomputable def cell1839 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1839.certificate 1483 accepted1839
noncomputable def cells : List CertifiedMinorantCell := [cell1832, cell1833, cell1834, cell1835, cell1836, cell1837, cell1838, cell1839]
theorem chainAccepted : minorantChainCheck (877/1000) (881/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (877/1000) (881/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0229
