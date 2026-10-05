import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0168
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0168
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1344 : minorantGammaCheck GammaPanel1344.certificate 1216=true := by decide +kernel
noncomputable def cell1344 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1344.certificate 1216 accepted1344
theorem accepted1345 : minorantGammaCheck GammaPanel1345.certificate 1216=true := by decide +kernel
noncomputable def cell1345 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1345.certificate 1216 accepted1345
theorem accepted1346 : minorantGammaCheck GammaPanel1346.certificate 1217=true := by decide +kernel
noncomputable def cell1346 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1346.certificate 1217 accepted1346
theorem accepted1347 : minorantGammaCheck GammaPanel1347.certificate 1218=true := by decide +kernel
noncomputable def cell1347 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1347.certificate 1218 accepted1347
theorem accepted1348 : minorantGammaCheck GammaPanel1348.certificate 1219=true := by decide +kernel
noncomputable def cell1348 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1348.certificate 1219 accepted1348
theorem accepted1349 : minorantGammaCheck GammaPanel1349.certificate 1220=true := by decide +kernel
noncomputable def cell1349 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1349.certificate 1220 accepted1349
theorem accepted1350 : minorantGammaCheck GammaPanel1350.certificate 1221=true := by decide +kernel
noncomputable def cell1350 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1350.certificate 1221 accepted1350
theorem accepted1351 : minorantGammaCheck GammaPanel1351.certificate 1222=true := by decide +kernel
noncomputable def cell1351 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1351.certificate 1222 accepted1351
noncomputable def cells : List CertifiedMinorantCell := [cell1344, cell1345, cell1346, cell1347, cell1348, cell1349, cell1350, cell1351]
theorem chainAccepted : minorantChainCheck (813/1000) (817/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (813/1000) (817/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0168
