import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0187
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0187
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1496 : minorantGammaCheck GammaPanel1496.certificate 1254=true := by decide +kernel
noncomputable def cell1496 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1496.certificate 1254 accepted1496
theorem accepted1497 : minorantGammaCheck GammaPanel1497.certificate 1255=true := by decide +kernel
noncomputable def cell1497 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1497.certificate 1255 accepted1497
theorem accepted1498 : minorantGammaCheck GammaPanel1498.certificate 1256=true := by decide +kernel
noncomputable def cell1498 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1498.certificate 1256 accepted1498
theorem accepted1499 : minorantGammaCheck GammaPanel1499.certificate 1257=true := by decide +kernel
noncomputable def cell1499 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1499.certificate 1257 accepted1499
theorem accepted1500 : minorantGammaCheck GammaPanel1500.certificate 1258=true := by decide +kernel
noncomputable def cell1500 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1500.certificate 1258 accepted1500
theorem accepted1501 : minorantGammaCheck GammaPanel1501.certificate 1259=true := by decide +kernel
noncomputable def cell1501 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1501.certificate 1259 accepted1501
theorem accepted1502 : minorantGammaCheck GammaPanel1502.certificate 1260=true := by decide +kernel
noncomputable def cell1502 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1502.certificate 1260 accepted1502
theorem accepted1503 : minorantGammaCheck GammaPanel1503.certificate 1261=true := by decide +kernel
noncomputable def cell1503 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1503.certificate 1261 accepted1503
noncomputable def cells : List CertifiedMinorantCell := [cell1496, cell1497, cell1498, cell1499, cell1500, cell1501, cell1502, cell1503]
theorem chainAccepted : minorantChainCheck (4209/5000) (4213/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4209/5000) (4213/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0187
