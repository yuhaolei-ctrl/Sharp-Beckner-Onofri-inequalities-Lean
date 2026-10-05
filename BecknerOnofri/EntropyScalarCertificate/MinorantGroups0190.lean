import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0190
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0190
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1520 : minorantGammaCheck GammaPanel1520.certificate 1278=true := by decide +kernel
noncomputable def cell1520 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1520.certificate 1278 accepted1520
theorem accepted1521 : minorantGammaCheck GammaPanel1521.certificate 1279=true := by decide +kernel
noncomputable def cell1521 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1521.certificate 1279 accepted1521
theorem accepted1522 : minorantGammaCheck GammaPanel1522.certificate 1280=true := by decide +kernel
noncomputable def cell1522 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1522.certificate 1280 accepted1522
theorem accepted1523 : minorantGammaCheck GammaPanel1523.certificate 1281=true := by decide +kernel
noncomputable def cell1523 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1523.certificate 1281 accepted1523
theorem accepted1524 : minorantGammaCheck GammaPanel1524.certificate 1282=true := by decide +kernel
noncomputable def cell1524 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1524.certificate 1282 accepted1524
theorem accepted1525 : minorantGammaCheck GammaPanel1525.certificate 1283=true := by decide +kernel
noncomputable def cell1525 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1525.certificate 1283 accepted1525
theorem accepted1526 : minorantGammaCheck GammaPanel1526.certificate 1284=true := by decide +kernel
noncomputable def cell1526 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1526.certificate 1284 accepted1526
theorem accepted1527 : minorantGammaCheck GammaPanel1527.certificate 1285=true := by decide +kernel
noncomputable def cell1527 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1527.certificate 1285 accepted1527
noncomputable def cells : List CertifiedMinorantCell := [cell1520, cell1521, cell1522, cell1523, cell1524, cell1525, cell1526, cell1527]
theorem chainAccepted : minorantChainCheck (4221/5000) (169/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4221/5000) (169/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0190
