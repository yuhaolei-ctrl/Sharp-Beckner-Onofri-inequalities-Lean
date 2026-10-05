import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0189
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0189
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1512 : minorantGammaCheck GammaPanel1512.certificate 1270=true := by decide +kernel
noncomputable def cell1512 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1512.certificate 1270 accepted1512
theorem accepted1513 : minorantGammaCheck GammaPanel1513.certificate 1271=true := by decide +kernel
noncomputable def cell1513 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1513.certificate 1271 accepted1513
theorem accepted1514 : minorantGammaCheck GammaPanel1514.certificate 1272=true := by decide +kernel
noncomputable def cell1514 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1514.certificate 1272 accepted1514
theorem accepted1515 : minorantGammaCheck GammaPanel1515.certificate 1273=true := by decide +kernel
noncomputable def cell1515 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1515.certificate 1273 accepted1515
theorem accepted1516 : minorantGammaCheck GammaPanel1516.certificate 1274=true := by decide +kernel
noncomputable def cell1516 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1516.certificate 1274 accepted1516
theorem accepted1517 : minorantGammaCheck GammaPanel1517.certificate 1275=true := by decide +kernel
noncomputable def cell1517 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1517.certificate 1275 accepted1517
theorem accepted1518 : minorantGammaCheck GammaPanel1518.certificate 1276=true := by decide +kernel
noncomputable def cell1518 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1518.certificate 1276 accepted1518
theorem accepted1519 : minorantGammaCheck GammaPanel1519.certificate 1277=true := by decide +kernel
noncomputable def cell1519 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1519.certificate 1277 accepted1519
noncomputable def cells : List CertifiedMinorantCell := [cell1512, cell1513, cell1514, cell1515, cell1516, cell1517, cell1518, cell1519]
theorem chainAccepted : minorantChainCheck (4217/5000) (4221/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4217/5000) (4221/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0189
