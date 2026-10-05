import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0238
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0238
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1904 : minorantGammaCheck GammaPanel1904.certificate 1548=true := by decide +kernel
noncomputable def cell1904 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1904.certificate 1548 accepted1904
theorem accepted1905 : minorantGammaCheck GammaPanel1905.certificate 1549=true := by decide +kernel
noncomputable def cell1905 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1905.certificate 1549 accepted1905
theorem accepted1906 : minorantGammaCheck GammaPanel1906.certificate 1550=true := by decide +kernel
noncomputable def cell1906 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1906.certificate 1550 accepted1906
theorem accepted1907 : minorantGammaCheck GammaPanel1907.certificate 1551=true := by decide +kernel
noncomputable def cell1907 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1907.certificate 1551 accepted1907
theorem accepted1908 : minorantGammaCheck GammaPanel1908.certificate 1552=true := by decide +kernel
noncomputable def cell1908 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1908.certificate 1552 accepted1908
theorem accepted1909 : minorantGammaCheck GammaPanel1909.certificate 1553=true := by decide +kernel
noncomputable def cell1909 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1909.certificate 1553 accepted1909
theorem accepted1910 : minorantGammaCheck GammaPanel1910.certificate 1554=true := by decide +kernel
noncomputable def cell1910 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1910.certificate 1554 accepted1910
theorem accepted1911 : minorantGammaCheck GammaPanel1911.certificate 1555=true := by decide +kernel
noncomputable def cell1911 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1911.certificate 1555 accepted1911
noncomputable def cells : List CertifiedMinorantCell := [cell1904, cell1905, cell1906, cell1907, cell1908, cell1909, cell1910, cell1911]
theorem chainAccepted : minorantChainCheck (913/1000) (917/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (913/1000) (917/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0238
