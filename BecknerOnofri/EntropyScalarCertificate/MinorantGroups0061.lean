import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0061
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0061
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0488 : minorantGammaCheck GammaPanel0488.certificate 448=true := by decide +kernel
noncomputable def cell0488 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0488.certificate 448 accepted0488
theorem accepted0489 : minorantGammaCheck GammaPanel0489.certificate 449=true := by decide +kernel
noncomputable def cell0489 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0489.certificate 449 accepted0489
theorem accepted0490 : minorantGammaCheck GammaPanel0490.certificate 450=true := by decide +kernel
noncomputable def cell0490 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0490.certificate 450 accepted0490
theorem accepted0491 : minorantGammaCheck GammaPanel0491.certificate 451=true := by decide +kernel
noncomputable def cell0491 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0491.certificate 451 accepted0491
theorem accepted0492 : minorantGammaCheck GammaPanel0492.certificate 452=true := by decide +kernel
noncomputable def cell0492 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0492.certificate 452 accepted0492
theorem accepted0493 : minorantGammaCheck GammaPanel0493.certificate 453=true := by decide +kernel
noncomputable def cell0493 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0493.certificate 453 accepted0493
theorem accepted0494 : minorantGammaCheck GammaPanel0494.certificate 454=true := by decide +kernel
noncomputable def cell0494 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0494.certificate 454 accepted0494
theorem accepted0495 : minorantGammaCheck GammaPanel0495.certificate 455=true := by decide +kernel
noncomputable def cell0495 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0495.certificate 455 accepted0495
noncomputable def cells : List CertifiedMinorantCell := [cell0488, cell0489, cell0490, cell0491, cell0492, cell0493, cell0494, cell0495]
theorem chainAccepted : minorantChainCheck (1541/10000) (1557/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1541/10000) (1557/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0061
