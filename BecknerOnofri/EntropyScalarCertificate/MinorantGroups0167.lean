import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0167
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0167
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1336 : minorantGammaCheck GammaPanel1336.certificate 1216=true := by decide +kernel
noncomputable def cell1336 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1336.certificate 1216 accepted1336
theorem accepted1337 : minorantGammaCheck GammaPanel1337.certificate 1216=true := by decide +kernel
noncomputable def cell1337 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1337.certificate 1216 accepted1337
theorem accepted1338 : minorantGammaCheck GammaPanel1338.certificate 1216=true := by decide +kernel
noncomputable def cell1338 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1338.certificate 1216 accepted1338
theorem accepted1339 : minorantGammaCheck GammaPanel1339.certificate 1216=true := by decide +kernel
noncomputable def cell1339 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1339.certificate 1216 accepted1339
theorem accepted1340 : minorantGammaCheck GammaPanel1340.certificate 1216=true := by decide +kernel
noncomputable def cell1340 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1340.certificate 1216 accepted1340
theorem accepted1341 : minorantGammaCheck GammaPanel1341.certificate 1216=true := by decide +kernel
noncomputable def cell1341 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1341.certificate 1216 accepted1341
theorem accepted1342 : minorantGammaCheck GammaPanel1342.certificate 1216=true := by decide +kernel
noncomputable def cell1342 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1342.certificate 1216 accepted1342
theorem accepted1343 : minorantGammaCheck GammaPanel1343.certificate 1216=true := by decide +kernel
noncomputable def cell1343 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1343.certificate 1216 accepted1343
noncomputable def cells : List CertifiedMinorantCell := [cell1336, cell1337, cell1338, cell1339, cell1340, cell1341, cell1342, cell1343]
theorem chainAccepted : minorantChainCheck (809/1000) (813/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (809/1000) (813/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0167
