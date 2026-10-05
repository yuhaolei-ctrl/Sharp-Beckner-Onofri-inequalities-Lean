import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0188
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0188
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1504 : minorantGammaCheck GammaPanel1504.certificate 1262=true := by decide +kernel
noncomputable def cell1504 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1504.certificate 1262 accepted1504
theorem accepted1505 : minorantGammaCheck GammaPanel1505.certificate 1263=true := by decide +kernel
noncomputable def cell1505 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1505.certificate 1263 accepted1505
theorem accepted1506 : minorantGammaCheck GammaPanel1506.certificate 1264=true := by decide +kernel
noncomputable def cell1506 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1506.certificate 1264 accepted1506
theorem accepted1507 : minorantGammaCheck GammaPanel1507.certificate 1265=true := by decide +kernel
noncomputable def cell1507 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1507.certificate 1265 accepted1507
theorem accepted1508 : minorantGammaCheck GammaPanel1508.certificate 1266=true := by decide +kernel
noncomputable def cell1508 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1508.certificate 1266 accepted1508
theorem accepted1509 : minorantGammaCheck GammaPanel1509.certificate 1267=true := by decide +kernel
noncomputable def cell1509 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1509.certificate 1267 accepted1509
theorem accepted1510 : minorantGammaCheck GammaPanel1510.certificate 1268=true := by decide +kernel
noncomputable def cell1510 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1510.certificate 1268 accepted1510
theorem accepted1511 : minorantGammaCheck GammaPanel1511.certificate 1269=true := by decide +kernel
noncomputable def cell1511 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1511.certificate 1269 accepted1511
noncomputable def cells : List CertifiedMinorantCell := [cell1504, cell1505, cell1506, cell1507, cell1508, cell1509, cell1510, cell1511]
theorem chainAccepted : minorantChainCheck (4213/5000) (4217/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4213/5000) (4217/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0188
