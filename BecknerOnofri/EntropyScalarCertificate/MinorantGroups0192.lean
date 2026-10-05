import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0192
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0192
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1536 : minorantGammaCheck GammaPanel1536.certificate 1294=true := by decide +kernel
noncomputable def cell1536 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1536.certificate 1294 accepted1536
theorem accepted1537 : minorantGammaCheck GammaPanel1537.certificate 1295=true := by decide +kernel
noncomputable def cell1537 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1537.certificate 1295 accepted1537
theorem accepted1538 : minorantGammaCheck GammaPanel1538.certificate 1296=true := by decide +kernel
noncomputable def cell1538 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1538.certificate 1296 accepted1538
theorem accepted1539 : minorantGammaCheck GammaPanel1539.certificate 1297=true := by decide +kernel
noncomputable def cell1539 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1539.certificate 1297 accepted1539
theorem accepted1540 : minorantGammaCheck GammaPanel1540.certificate 1298=true := by decide +kernel
noncomputable def cell1540 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1540.certificate 1298 accepted1540
theorem accepted1541 : minorantGammaCheck GammaPanel1541.certificate 1299=true := by decide +kernel
noncomputable def cell1541 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1541.certificate 1299 accepted1541
theorem accepted1542 : minorantGammaCheck GammaPanel1542.certificate 1300=true := by decide +kernel
noncomputable def cell1542 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1542.certificate 1300 accepted1542
theorem accepted1543 : minorantGammaCheck GammaPanel1543.certificate 1301=true := by decide +kernel
noncomputable def cell1543 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1543.certificate 1301 accepted1543
noncomputable def cells : List CertifiedMinorantCell := [cell1536, cell1537, cell1538, cell1539, cell1540, cell1541, cell1542, cell1543]
theorem chainAccepted : minorantChainCheck (4229/5000) (4233/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4229/5000) (4233/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0192
