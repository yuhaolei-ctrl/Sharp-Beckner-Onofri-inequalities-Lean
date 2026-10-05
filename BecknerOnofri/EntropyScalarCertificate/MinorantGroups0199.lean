import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0199
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0199
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1592 : minorantGammaCheck GammaPanel1592.certificate 1350=true := by decide +kernel
noncomputable def cell1592 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1592.certificate 1350 accepted1592
theorem accepted1593 : minorantGammaCheck GammaPanel1593.certificate 1351=true := by decide +kernel
noncomputable def cell1593 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1593.certificate 1351 accepted1593
theorem accepted1594 : minorantGammaCheck GammaPanel1594.certificate 1352=true := by decide +kernel
noncomputable def cell1594 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1594.certificate 1352 accepted1594
theorem accepted1595 : minorantGammaCheck GammaPanel1595.certificate 1353=true := by decide +kernel
noncomputable def cell1595 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1595.certificate 1353 accepted1595
theorem accepted1596 : minorantGammaCheck GammaPanel1596.certificate 1354=true := by decide +kernel
noncomputable def cell1596 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1596.certificate 1354 accepted1596
theorem accepted1597 : minorantGammaCheck GammaPanel1597.certificate 1355=true := by decide +kernel
noncomputable def cell1597 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1597.certificate 1355 accepted1597
theorem accepted1598 : minorantGammaCheck GammaPanel1598.certificate 1356=true := by decide +kernel
noncomputable def cell1598 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1598.certificate 1356 accepted1598
theorem accepted1599 : minorantGammaCheck GammaPanel1599.certificate 1357=true := by decide +kernel
noncomputable def cell1599 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1599.certificate 1357 accepted1599
noncomputable def cells : List CertifiedMinorantCell := [cell1592, cell1593, cell1594, cell1595, cell1596, cell1597, cell1598, cell1599]
theorem chainAccepted : minorantChainCheck (4257/5000) (4261/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4257/5000) (4261/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0199
