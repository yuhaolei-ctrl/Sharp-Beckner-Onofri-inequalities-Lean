import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0176
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0176
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1408 : minorantGammaCheck GammaPanel1408.certificate 1249=true := by decide +kernel
noncomputable def cell1408 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1408.certificate 1249 accepted1408
theorem accepted1409 : minorantGammaCheck GammaPanel1409.certificate 1249=true := by decide +kernel
noncomputable def cell1409 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1409.certificate 1249 accepted1409
theorem accepted1410 : minorantGammaCheck GammaPanel1410.certificate 1249=true := by decide +kernel
noncomputable def cell1410 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1410.certificate 1249 accepted1410
theorem accepted1411 : minorantGammaCheck GammaPanel1411.certificate 1249=true := by decide +kernel
noncomputable def cell1411 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1411.certificate 1249 accepted1411
theorem accepted1412 : minorantGammaCheck GammaPanel1412.certificate 1249=true := by decide +kernel
noncomputable def cell1412 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1412.certificate 1249 accepted1412
theorem accepted1413 : minorantGammaCheck GammaPanel1413.certificate 1249=true := by decide +kernel
noncomputable def cell1413 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1413.certificate 1249 accepted1413
theorem accepted1414 : minorantGammaCheck GammaPanel1414.certificate 1249=true := by decide +kernel
noncomputable def cell1414 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1414.certificate 1249 accepted1414
theorem accepted1415 : minorantGammaCheck GammaPanel1415.certificate 1249=true := by decide +kernel
noncomputable def cell1415 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1415.certificate 1249 accepted1415
noncomputable def cells : List CertifiedMinorantCell := [cell1408, cell1409, cell1410, cell1411, cell1412, cell1413, cell1414, cell1415]
theorem chainAccepted : minorantChainCheck (833/1000) (4169/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (833/1000) (4169/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0176
