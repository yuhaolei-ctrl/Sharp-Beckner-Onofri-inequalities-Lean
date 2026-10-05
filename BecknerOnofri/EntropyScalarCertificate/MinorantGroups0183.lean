import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0183
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0183
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1464 : minorantGammaCheck GammaPanel1464.certificate 1249=true := by decide +kernel
noncomputable def cell1464 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1464.certificate 1249 accepted1464
theorem accepted1465 : minorantGammaCheck GammaPanel1465.certificate 1249=true := by decide +kernel
noncomputable def cell1465 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1465.certificate 1249 accepted1465
theorem accepted1466 : minorantGammaCheck GammaPanel1466.certificate 1249=true := by decide +kernel
noncomputable def cell1466 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1466.certificate 1249 accepted1466
theorem accepted1467 : minorantGammaCheck GammaPanel1467.certificate 1249=true := by decide +kernel
noncomputable def cell1467 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1467.certificate 1249 accepted1467
theorem accepted1468 : minorantGammaCheck GammaPanel1468.certificate 1249=true := by decide +kernel
noncomputable def cell1468 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1468.certificate 1249 accepted1468
theorem accepted1469 : minorantGammaCheck GammaPanel1469.certificate 1249=true := by decide +kernel
noncomputable def cell1469 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1469.certificate 1249 accepted1469
theorem accepted1470 : minorantGammaCheck GammaPanel1470.certificate 1249=true := by decide +kernel
noncomputable def cell1470 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1470.certificate 1249 accepted1470
theorem accepted1471 : minorantGammaCheck GammaPanel1471.certificate 1249=true := by decide +kernel
noncomputable def cell1471 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1471.certificate 1249 accepted1471
noncomputable def cells : List CertifiedMinorantCell := [cell1464, cell1465, cell1466, cell1467, cell1468, cell1469, cell1470, cell1471]
theorem chainAccepted : minorantChainCheck (4193/5000) (4197/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4193/5000) (4197/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0183
