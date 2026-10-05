import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0181
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0181
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1448 : minorantGammaCheck GammaPanel1448.certificate 1249=true := by decide +kernel
noncomputable def cell1448 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1448.certificate 1249 accepted1448
theorem accepted1449 : minorantGammaCheck GammaPanel1449.certificate 1249=true := by decide +kernel
noncomputable def cell1449 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1449.certificate 1249 accepted1449
theorem accepted1450 : minorantGammaCheck GammaPanel1450.certificate 1249=true := by decide +kernel
noncomputable def cell1450 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1450.certificate 1249 accepted1450
theorem accepted1451 : minorantGammaCheck GammaPanel1451.certificate 1249=true := by decide +kernel
noncomputable def cell1451 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1451.certificate 1249 accepted1451
theorem accepted1452 : minorantGammaCheck GammaPanel1452.certificate 1249=true := by decide +kernel
noncomputable def cell1452 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1452.certificate 1249 accepted1452
theorem accepted1453 : minorantGammaCheck GammaPanel1453.certificate 1249=true := by decide +kernel
noncomputable def cell1453 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1453.certificate 1249 accepted1453
theorem accepted1454 : minorantGammaCheck GammaPanel1454.certificate 1249=true := by decide +kernel
noncomputable def cell1454 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1454.certificate 1249 accepted1454
theorem accepted1455 : minorantGammaCheck GammaPanel1455.certificate 1249=true := by decide +kernel
noncomputable def cell1455 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1455.certificate 1249 accepted1455
noncomputable def cells : List CertifiedMinorantCell := [cell1448, cell1449, cell1450, cell1451, cell1452, cell1453, cell1454, cell1455]
theorem chainAccepted : minorantChainCheck (837/1000) (4189/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (837/1000) (4189/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0181
