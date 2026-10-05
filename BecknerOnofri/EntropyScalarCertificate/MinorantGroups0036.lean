import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0036
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0036
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0288 : minorantGammaCheck GammaPanel0288.certificate 248=true := by decide +kernel
noncomputable def cell0288 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0288.certificate 248 accepted0288
theorem accepted0289 : minorantGammaCheck GammaPanel0289.certificate 249=true := by decide +kernel
noncomputable def cell0289 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0289.certificate 249 accepted0289
theorem accepted0290 : minorantGammaCheck GammaPanel0290.certificate 250=true := by decide +kernel
noncomputable def cell0290 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0290.certificate 250 accepted0290
theorem accepted0291 : minorantGammaCheck GammaPanel0291.certificate 251=true := by decide +kernel
noncomputable def cell0291 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0291.certificate 251 accepted0291
theorem accepted0292 : minorantGammaCheck GammaPanel0292.certificate 252=true := by decide +kernel
noncomputable def cell0292 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0292.certificate 252 accepted0292
theorem accepted0293 : minorantGammaCheck GammaPanel0293.certificate 253=true := by decide +kernel
noncomputable def cell0293 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0293.certificate 253 accepted0293
theorem accepted0294 : minorantGammaCheck GammaPanel0294.certificate 254=true := by decide +kernel
noncomputable def cell0294 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0294.certificate 254 accepted0294
theorem accepted0295 : minorantGammaCheck GammaPanel0295.certificate 255=true := by decide +kernel
noncomputable def cell0295 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0295.certificate 255 accepted0295
noncomputable def cells : List CertifiedMinorantCell := [cell0288, cell0289, cell0290, cell0291, cell0292, cell0293, cell0294, cell0295]
theorem chainAccepted : minorantChainCheck (1141/10000) (1157/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1141/10000) (1157/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0036
