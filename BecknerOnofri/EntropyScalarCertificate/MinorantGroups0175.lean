import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0175
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0175
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1400 : minorantGammaCheck GammaPanel1400.certificate 1249=true := by decide +kernel
noncomputable def cell1400 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1400.certificate 1249 accepted1400
theorem accepted1401 : minorantGammaCheck GammaPanel1401.certificate 1249=true := by decide +kernel
noncomputable def cell1401 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1401.certificate 1249 accepted1401
theorem accepted1402 : minorantGammaCheck GammaPanel1402.certificate 1249=true := by decide +kernel
noncomputable def cell1402 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1402.certificate 1249 accepted1402
theorem accepted1403 : minorantGammaCheck GammaPanel1403.certificate 1249=true := by decide +kernel
noncomputable def cell1403 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1403.certificate 1249 accepted1403
theorem accepted1404 : minorantGammaCheck GammaPanel1404.certificate 1249=true := by decide +kernel
noncomputable def cell1404 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1404.certificate 1249 accepted1404
theorem accepted1405 : minorantGammaCheck GammaPanel1405.certificate 1249=true := by decide +kernel
noncomputable def cell1405 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1405.certificate 1249 accepted1405
theorem accepted1406 : minorantGammaCheck GammaPanel1406.certificate 1249=true := by decide +kernel
noncomputable def cell1406 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1406.certificate 1249 accepted1406
theorem accepted1407 : minorantGammaCheck GammaPanel1407.certificate 1249=true := by decide +kernel
noncomputable def cell1407 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1407.certificate 1249 accepted1407
noncomputable def cells : List CertifiedMinorantCell := [cell1400, cell1401, cell1402, cell1403, cell1404, cell1405, cell1406, cell1407]
theorem chainAccepted : minorantChainCheck (4161/5000) (833/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4161/5000) (833/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0175
