import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0163
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0163
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1304 : minorantGammaCheck GammaPanel1304.certificate 1202=true := by decide +kernel
noncomputable def cell1304 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1304.certificate 1202 accepted1304
theorem accepted1305 : minorantGammaCheck GammaPanel1305.certificate 1203=true := by decide +kernel
noncomputable def cell1305 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1305.certificate 1203 accepted1305
theorem accepted1306 : minorantGammaCheck GammaPanel1306.certificate 1204=true := by decide +kernel
noncomputable def cell1306 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1306.certificate 1204 accepted1306
theorem accepted1307 : minorantGammaCheck GammaPanel1307.certificate 1205=true := by decide +kernel
noncomputable def cell1307 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1307.certificate 1205 accepted1307
theorem accepted1308 : minorantGammaCheck GammaPanel1308.certificate 1206=true := by decide +kernel
noncomputable def cell1308 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1308.certificate 1206 accepted1308
theorem accepted1309 : minorantGammaCheck GammaPanel1309.certificate 1207=true := by decide +kernel
noncomputable def cell1309 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1309.certificate 1207 accepted1309
theorem accepted1310 : minorantGammaCheck GammaPanel1310.certificate 1208=true := by decide +kernel
noncomputable def cell1310 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1310.certificate 1208 accepted1310
theorem accepted1311 : minorantGammaCheck GammaPanel1311.certificate 1209=true := by decide +kernel
noncomputable def cell1311 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1311.certificate 1209 accepted1311
noncomputable def cells : List CertifiedMinorantCell := [cell1304, cell1305, cell1306, cell1307, cell1308, cell1309, cell1310, cell1311]
theorem chainAccepted : minorantChainCheck (393/500) (397/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (393/500) (397/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0163
