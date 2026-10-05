import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0161
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0161
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1288 : minorantGammaCheck GammaPanel1288.certificate 1186=true := by decide +kernel
noncomputable def cell1288 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1288.certificate 1186 accepted1288
theorem accepted1289 : minorantGammaCheck GammaPanel1289.certificate 1187=true := by decide +kernel
noncomputable def cell1289 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1289.certificate 1187 accepted1289
theorem accepted1290 : minorantGammaCheck GammaPanel1290.certificate 1188=true := by decide +kernel
noncomputable def cell1290 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1290.certificate 1188 accepted1290
theorem accepted1291 : minorantGammaCheck GammaPanel1291.certificate 1189=true := by decide +kernel
noncomputable def cell1291 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1291.certificate 1189 accepted1291
theorem accepted1292 : minorantGammaCheck GammaPanel1292.certificate 1190=true := by decide +kernel
noncomputable def cell1292 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1292.certificate 1190 accepted1292
theorem accepted1293 : minorantGammaCheck GammaPanel1293.certificate 1191=true := by decide +kernel
noncomputable def cell1293 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1293.certificate 1191 accepted1293
theorem accepted1294 : minorantGammaCheck GammaPanel1294.certificate 1192=true := by decide +kernel
noncomputable def cell1294 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1294.certificate 1192 accepted1294
theorem accepted1295 : minorantGammaCheck GammaPanel1295.certificate 1193=true := by decide +kernel
noncomputable def cell1295 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1295.certificate 1193 accepted1295
noncomputable def cells : List CertifiedMinorantCell := [cell1288, cell1289, cell1290, cell1291, cell1292, cell1293, cell1294, cell1295]
theorem chainAccepted : minorantChainCheck (77/100) (389/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (77/100) (389/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0161
