import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0185
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0185
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1480 : minorantGammaCheck GammaPanel1480.certificate 1249=true := by decide +kernel
noncomputable def cell1480 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1480.certificate 1249 accepted1480
theorem accepted1481 : minorantGammaCheck GammaPanel1481.certificate 1249=true := by decide +kernel
noncomputable def cell1481 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1481.certificate 1249 accepted1481
theorem accepted1482 : minorantGammaCheck GammaPanel1482.certificate 1249=true := by decide +kernel
noncomputable def cell1482 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1482.certificate 1249 accepted1482
theorem accepted1483 : minorantGammaCheck GammaPanel1483.certificate 1249=true := by decide +kernel
noncomputable def cell1483 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1483.certificate 1249 accepted1483
theorem accepted1484 : minorantGammaCheck GammaPanel1484.certificate 1249=true := by decide +kernel
noncomputable def cell1484 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1484.certificate 1249 accepted1484
theorem accepted1485 : minorantGammaCheck GammaPanel1485.certificate 1249=true := by decide +kernel
noncomputable def cell1485 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1485.certificate 1249 accepted1485
theorem accepted1486 : minorantGammaCheck GammaPanel1486.certificate 1249=true := by decide +kernel
noncomputable def cell1486 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1486.certificate 1249 accepted1486
theorem accepted1487 : minorantGammaCheck GammaPanel1487.certificate 1249=true := by decide +kernel
noncomputable def cell1487 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1487.certificate 1249 accepted1487
noncomputable def cells : List CertifiedMinorantCell := [cell1480, cell1481, cell1482, cell1483, cell1484, cell1485, cell1486, cell1487]
theorem chainAccepted : minorantChainCheck (4201/5000) (841/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4201/5000) (841/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0185
