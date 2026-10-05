import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0180
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0180
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1440 : minorantGammaCheck GammaPanel1440.certificate 1249=true := by decide +kernel
noncomputable def cell1440 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1440.certificate 1249 accepted1440
theorem accepted1441 : minorantGammaCheck GammaPanel1441.certificate 1249=true := by decide +kernel
noncomputable def cell1441 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1441.certificate 1249 accepted1441
theorem accepted1442 : minorantGammaCheck GammaPanel1442.certificate 1249=true := by decide +kernel
noncomputable def cell1442 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1442.certificate 1249 accepted1442
theorem accepted1443 : minorantGammaCheck GammaPanel1443.certificate 1249=true := by decide +kernel
noncomputable def cell1443 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1443.certificate 1249 accepted1443
theorem accepted1444 : minorantGammaCheck GammaPanel1444.certificate 1249=true := by decide +kernel
noncomputable def cell1444 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1444.certificate 1249 accepted1444
theorem accepted1445 : minorantGammaCheck GammaPanel1445.certificate 1249=true := by decide +kernel
noncomputable def cell1445 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1445.certificate 1249 accepted1445
theorem accepted1446 : minorantGammaCheck GammaPanel1446.certificate 1249=true := by decide +kernel
noncomputable def cell1446 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1446.certificate 1249 accepted1446
theorem accepted1447 : minorantGammaCheck GammaPanel1447.certificate 1249=true := by decide +kernel
noncomputable def cell1447 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1447.certificate 1249 accepted1447
noncomputable def cells : List CertifiedMinorantCell := [cell1440, cell1441, cell1442, cell1443, cell1444, cell1445, cell1446, cell1447]
theorem chainAccepted : minorantChainCheck (4181/5000) (837/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4181/5000) (837/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0180
