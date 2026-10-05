import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0177
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0177
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1416 : minorantGammaCheck GammaPanel1416.certificate 1249=true := by decide +kernel
noncomputable def cell1416 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1416.certificate 1249 accepted1416
theorem accepted1417 : minorantGammaCheck GammaPanel1417.certificate 1249=true := by decide +kernel
noncomputable def cell1417 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1417.certificate 1249 accepted1417
theorem accepted1418 : minorantGammaCheck GammaPanel1418.certificate 1249=true := by decide +kernel
noncomputable def cell1418 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1418.certificate 1249 accepted1418
theorem accepted1419 : minorantGammaCheck GammaPanel1419.certificate 1249=true := by decide +kernel
noncomputable def cell1419 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1419.certificate 1249 accepted1419
theorem accepted1420 : minorantGammaCheck GammaPanel1420.certificate 1249=true := by decide +kernel
noncomputable def cell1420 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1420.certificate 1249 accepted1420
theorem accepted1421 : minorantGammaCheck GammaPanel1421.certificate 1249=true := by decide +kernel
noncomputable def cell1421 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1421.certificate 1249 accepted1421
theorem accepted1422 : minorantGammaCheck GammaPanel1422.certificate 1249=true := by decide +kernel
noncomputable def cell1422 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1422.certificate 1249 accepted1422
theorem accepted1423 : minorantGammaCheck GammaPanel1423.certificate 1249=true := by decide +kernel
noncomputable def cell1423 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1423.certificate 1249 accepted1423
noncomputable def cells : List CertifiedMinorantCell := [cell1416, cell1417, cell1418, cell1419, cell1420, cell1421, cell1422, cell1423]
theorem chainAccepted : minorantChainCheck (4169/5000) (4173/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4169/5000) (4173/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0177
