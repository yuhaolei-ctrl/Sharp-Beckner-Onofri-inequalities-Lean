import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0184
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0184
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1472 : minorantGammaCheck GammaPanel1472.certificate 1249=true := by decide +kernel
noncomputable def cell1472 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1472.certificate 1249 accepted1472
theorem accepted1473 : minorantGammaCheck GammaPanel1473.certificate 1249=true := by decide +kernel
noncomputable def cell1473 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1473.certificate 1249 accepted1473
theorem accepted1474 : minorantGammaCheck GammaPanel1474.certificate 1249=true := by decide +kernel
noncomputable def cell1474 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1474.certificate 1249 accepted1474
theorem accepted1475 : minorantGammaCheck GammaPanel1475.certificate 1249=true := by decide +kernel
noncomputable def cell1475 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1475.certificate 1249 accepted1475
theorem accepted1476 : minorantGammaCheck GammaPanel1476.certificate 1249=true := by decide +kernel
noncomputable def cell1476 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1476.certificate 1249 accepted1476
theorem accepted1477 : minorantGammaCheck GammaPanel1477.certificate 1249=true := by decide +kernel
noncomputable def cell1477 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1477.certificate 1249 accepted1477
theorem accepted1478 : minorantGammaCheck GammaPanel1478.certificate 1249=true := by decide +kernel
noncomputable def cell1478 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1478.certificate 1249 accepted1478
theorem accepted1479 : minorantGammaCheck GammaPanel1479.certificate 1249=true := by decide +kernel
noncomputable def cell1479 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1479.certificate 1249 accepted1479
noncomputable def cells : List CertifiedMinorantCell := [cell1472, cell1473, cell1474, cell1475, cell1476, cell1477, cell1478, cell1479]
theorem chainAccepted : minorantChainCheck (4197/5000) (4201/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4197/5000) (4201/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0184
