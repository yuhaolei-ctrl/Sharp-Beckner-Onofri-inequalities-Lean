import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0059
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0059
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0472 : minorantGammaCheck GammaPanel0472.certificate 432=true := by decide +kernel
noncomputable def cell0472 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0472.certificate 432 accepted0472
theorem accepted0473 : minorantGammaCheck GammaPanel0473.certificate 433=true := by decide +kernel
noncomputable def cell0473 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0473.certificate 433 accepted0473
theorem accepted0474 : minorantGammaCheck GammaPanel0474.certificate 434=true := by decide +kernel
noncomputable def cell0474 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0474.certificate 434 accepted0474
theorem accepted0475 : minorantGammaCheck GammaPanel0475.certificate 435=true := by decide +kernel
noncomputable def cell0475 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0475.certificate 435 accepted0475
theorem accepted0476 : minorantGammaCheck GammaPanel0476.certificate 436=true := by decide +kernel
noncomputable def cell0476 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0476.certificate 436 accepted0476
theorem accepted0477 : minorantGammaCheck GammaPanel0477.certificate 437=true := by decide +kernel
noncomputable def cell0477 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0477.certificate 437 accepted0477
theorem accepted0478 : minorantGammaCheck GammaPanel0478.certificate 438=true := by decide +kernel
noncomputable def cell0478 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0478.certificate 438 accepted0478
theorem accepted0479 : minorantGammaCheck GammaPanel0479.certificate 439=true := by decide +kernel
noncomputable def cell0479 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0479.certificate 439 accepted0479
noncomputable def cells : List CertifiedMinorantCell := [cell0472, cell0473, cell0474, cell0475, cell0476, cell0477, cell0478, cell0479]
theorem chainAccepted : minorantChainCheck (1509/10000) (61/400) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1509/10000) (61/400) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0059
