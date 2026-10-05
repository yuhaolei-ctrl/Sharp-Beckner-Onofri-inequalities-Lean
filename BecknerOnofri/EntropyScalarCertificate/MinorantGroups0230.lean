import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0230
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0230
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1840 : minorantGammaCheck GammaPanel1840.certificate 1484=true := by decide +kernel
noncomputable def cell1840 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1840.certificate 1484 accepted1840
theorem accepted1841 : minorantGammaCheck GammaPanel1841.certificate 1485=true := by decide +kernel
noncomputable def cell1841 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1841.certificate 1485 accepted1841
theorem accepted1842 : minorantGammaCheck GammaPanel1842.certificate 1486=true := by decide +kernel
noncomputable def cell1842 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1842.certificate 1486 accepted1842
theorem accepted1843 : minorantGammaCheck GammaPanel1843.certificate 1487=true := by decide +kernel
noncomputable def cell1843 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1843.certificate 1487 accepted1843
theorem accepted1844 : minorantGammaCheck GammaPanel1844.certificate 1488=true := by decide +kernel
noncomputable def cell1844 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1844.certificate 1488 accepted1844
theorem accepted1845 : minorantGammaCheck GammaPanel1845.certificate 1489=true := by decide +kernel
noncomputable def cell1845 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1845.certificate 1489 accepted1845
theorem accepted1846 : minorantGammaCheck GammaPanel1846.certificate 1490=true := by decide +kernel
noncomputable def cell1846 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1846.certificate 1490 accepted1846
theorem accepted1847 : minorantGammaCheck GammaPanel1847.certificate 1491=true := by decide +kernel
noncomputable def cell1847 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1847.certificate 1491 accepted1847
noncomputable def cells : List CertifiedMinorantCell := [cell1840, cell1841, cell1842, cell1843, cell1844, cell1845, cell1846, cell1847]
theorem chainAccepted : minorantChainCheck (881/1000) (177/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (881/1000) (177/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0230
