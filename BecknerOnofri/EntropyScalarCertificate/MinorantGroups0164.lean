import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0164
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0164
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1312 : minorantGammaCheck GammaPanel1312.certificate 1210=true := by decide +kernel
noncomputable def cell1312 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1312.certificate 1210 accepted1312
theorem accepted1313 : minorantGammaCheck GammaPanel1313.certificate 1211=true := by decide +kernel
noncomputable def cell1313 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1313.certificate 1211 accepted1313
theorem accepted1314 : minorantGammaCheck GammaPanel1314.certificate 1212=true := by decide +kernel
noncomputable def cell1314 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1314.certificate 1212 accepted1314
theorem accepted1315 : minorantGammaCheck GammaPanel1315.certificate 1213=true := by decide +kernel
noncomputable def cell1315 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1315.certificate 1213 accepted1315
theorem accepted1316 : minorantGammaCheck GammaPanel1316.certificate 1214=true := by decide +kernel
noncomputable def cell1316 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1316.certificate 1214 accepted1316
theorem accepted1317 : minorantGammaCheck GammaPanel1317.certificate 1215=true := by decide +kernel
noncomputable def cell1317 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1317.certificate 1215 accepted1317
theorem accepted1318 : minorantGammaCheck GammaPanel1318.certificate 1216=true := by decide +kernel
noncomputable def cell1318 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1318.certificate 1216 accepted1318
theorem accepted1319 : minorantGammaCheck GammaPanel1319.certificate 1216=true := by decide +kernel
noncomputable def cell1319 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1319.certificate 1216 accepted1319
noncomputable def cells : List CertifiedMinorantCell := [cell1312, cell1313, cell1314, cell1315, cell1316, cell1317, cell1318, cell1319]
theorem chainAccepted : minorantChainCheck (397/500) (801/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (397/500) (801/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0164
