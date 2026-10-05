module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0231

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0231
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1848 : minorantGammaCheck GammaPanel1848.certificate 1492=true := by decide +kernel
noncomputable def cell1848 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1848.certificate 1492 accepted1848
theorem accepted1849 : minorantGammaCheck GammaPanel1849.certificate 1493=true := by decide +kernel
noncomputable def cell1849 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1849.certificate 1493 accepted1849
theorem accepted1850 : minorantGammaCheck GammaPanel1850.certificate 1494=true := by decide +kernel
noncomputable def cell1850 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1850.certificate 1494 accepted1850
theorem accepted1851 : minorantGammaCheck GammaPanel1851.certificate 1495=true := by decide +kernel
noncomputable def cell1851 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1851.certificate 1495 accepted1851
theorem accepted1852 : minorantGammaCheck GammaPanel1852.certificate 1496=true := by decide +kernel
noncomputable def cell1852 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1852.certificate 1496 accepted1852
theorem accepted1853 : minorantGammaCheck GammaPanel1853.certificate 1497=true := by decide +kernel
noncomputable def cell1853 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1853.certificate 1497 accepted1853
theorem accepted1854 : minorantGammaCheck GammaPanel1854.certificate 1498=true := by decide +kernel
noncomputable def cell1854 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1854.certificate 1498 accepted1854
theorem accepted1855 : minorantGammaCheck GammaPanel1855.certificate 1499=true := by decide +kernel
noncomputable def cell1855 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1855.certificate 1499 accepted1855
noncomputable def cells : List CertifiedMinorantCell := [cell1848, cell1849, cell1850, cell1851, cell1852, cell1853, cell1854, cell1855]
theorem chainAccepted : minorantChainCheck (177/200) (889/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (177/200) (889/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0231
