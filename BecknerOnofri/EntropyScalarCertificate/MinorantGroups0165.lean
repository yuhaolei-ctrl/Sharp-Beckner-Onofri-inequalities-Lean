import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0165
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0165
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1320 : minorantGammaCheck GammaPanel1320.certificate 1216=true := by decide +kernel
noncomputable def cell1320 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1320.certificate 1216 accepted1320
theorem accepted1321 : minorantGammaCheck GammaPanel1321.certificate 1216=true := by decide +kernel
noncomputable def cell1321 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1321.certificate 1216 accepted1321
theorem accepted1322 : minorantGammaCheck GammaPanel1322.certificate 1216=true := by decide +kernel
noncomputable def cell1322 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1322.certificate 1216 accepted1322
theorem accepted1323 : minorantGammaCheck GammaPanel1323.certificate 1216=true := by decide +kernel
noncomputable def cell1323 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1323.certificate 1216 accepted1323
theorem accepted1324 : minorantGammaCheck GammaPanel1324.certificate 1216=true := by decide +kernel
noncomputable def cell1324 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1324.certificate 1216 accepted1324
theorem accepted1325 : minorantGammaCheck GammaPanel1325.certificate 1216=true := by decide +kernel
noncomputable def cell1325 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1325.certificate 1216 accepted1325
theorem accepted1326 : minorantGammaCheck GammaPanel1326.certificate 1216=true := by decide +kernel
noncomputable def cell1326 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1326.certificate 1216 accepted1326
theorem accepted1327 : minorantGammaCheck GammaPanel1327.certificate 1216=true := by decide +kernel
noncomputable def cell1327 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1327.certificate 1216 accepted1327
noncomputable def cells : List CertifiedMinorantCell := [cell1320, cell1321, cell1322, cell1323, cell1324, cell1325, cell1326, cell1327]
theorem chainAccepted : minorantChainCheck (801/1000) (161/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (801/1000) (161/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0165
