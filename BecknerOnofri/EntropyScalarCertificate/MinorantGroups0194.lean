import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0194
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0194
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1552 : minorantGammaCheck GammaPanel1552.certificate 1310=true := by decide +kernel
noncomputable def cell1552 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1552.certificate 1310 accepted1552
theorem accepted1553 : minorantGammaCheck GammaPanel1553.certificate 1311=true := by decide +kernel
noncomputable def cell1553 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1553.certificate 1311 accepted1553
theorem accepted1554 : minorantGammaCheck GammaPanel1554.certificate 1312=true := by decide +kernel
noncomputable def cell1554 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1554.certificate 1312 accepted1554
theorem accepted1555 : minorantGammaCheck GammaPanel1555.certificate 1313=true := by decide +kernel
noncomputable def cell1555 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1555.certificate 1313 accepted1555
theorem accepted1556 : minorantGammaCheck GammaPanel1556.certificate 1314=true := by decide +kernel
noncomputable def cell1556 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1556.certificate 1314 accepted1556
theorem accepted1557 : minorantGammaCheck GammaPanel1557.certificate 1315=true := by decide +kernel
noncomputable def cell1557 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1557.certificate 1315 accepted1557
theorem accepted1558 : minorantGammaCheck GammaPanel1558.certificate 1316=true := by decide +kernel
noncomputable def cell1558 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1558.certificate 1316 accepted1558
theorem accepted1559 : minorantGammaCheck GammaPanel1559.certificate 1317=true := by decide +kernel
noncomputable def cell1559 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1559.certificate 1317 accepted1559
noncomputable def cells : List CertifiedMinorantCell := [cell1552, cell1553, cell1554, cell1555, cell1556, cell1557, cell1558, cell1559]
theorem chainAccepted : minorantChainCheck (4237/5000) (4241/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4237/5000) (4241/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0194
