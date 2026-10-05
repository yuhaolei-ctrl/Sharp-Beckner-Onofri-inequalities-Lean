import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0055
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0055
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0440 : minorantGammaCheck GammaPanel0440.certificate 400=true := by decide +kernel
noncomputable def cell0440 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0440.certificate 400 accepted0440
theorem accepted0441 : minorantGammaCheck GammaPanel0441.certificate 401=true := by decide +kernel
noncomputable def cell0441 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0441.certificate 401 accepted0441
theorem accepted0442 : minorantGammaCheck GammaPanel0442.certificate 402=true := by decide +kernel
noncomputable def cell0442 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0442.certificate 402 accepted0442
theorem accepted0443 : minorantGammaCheck GammaPanel0443.certificate 403=true := by decide +kernel
noncomputable def cell0443 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0443.certificate 403 accepted0443
theorem accepted0444 : minorantGammaCheck GammaPanel0444.certificate 404=true := by decide +kernel
noncomputable def cell0444 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0444.certificate 404 accepted0444
theorem accepted0445 : minorantGammaCheck GammaPanel0445.certificate 405=true := by decide +kernel
noncomputable def cell0445 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0445.certificate 405 accepted0445
theorem accepted0446 : minorantGammaCheck GammaPanel0446.certificate 406=true := by decide +kernel
noncomputable def cell0446 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0446.certificate 406 accepted0446
theorem accepted0447 : minorantGammaCheck GammaPanel0447.certificate 407=true := by decide +kernel
noncomputable def cell0447 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0447.certificate 407 accepted0447
noncomputable def cells : List CertifiedMinorantCell := [cell0440, cell0441, cell0442, cell0443, cell0444, cell0445, cell0446, cell0447]
theorem chainAccepted : minorantChainCheck (289/2000) (1461/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (289/2000) (1461/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0055
